(** When Hello calls getopt_long for the first time, the parser reads
    objects that nothing has written since the loader built memory. They
    are glibc's private parser object, the flags opterr and optopt, the
    strings "--", "-" and "-W ", and Hello's option table with its four
    names and its option string. HelloGetoptStart.v takes the pieces of
    these objects from the starting memory at any addresses. This file
    shows that the memory the loader builds for the whole linked Hello
    image holds those pieces, at the addresses that its symbols give.

    We cannot compute the whole memory, because it is too large. Instead
    we load a copy of the image in which every other object is blank,
    and we read the twelve objects there. Those objects are the same in
    both memories, so their values carry over. A last theorem shows that
    one heap can own these objects together with the fifteen constants
    that gettext reads.

    This is a fact about initialized memory. It does not show that Hello
    starts from this memory, that a constructor leaves these objects
    alone, who owns the rest of memory, or that a startup proof runs
    this module. *)

From stdpp Require Import list.
From Stdlib Require Import String ZArith Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Run Pieces Heap.
From Glibc Require Import WordString GetoptInitial HelloGetoptTable HelloGetoptStart.
From Glibc Require Import HelloImageErase HelloImageEraseMem HelloImagePieces HelloImageCode HelloImageLoad
  HelloImageKept.
Import ListNotations.
Open Scope Z_scope.

(** ## The objects and their addresses

    The parser's three writable objects get capabilities of their own
    object, and the eight strings and the table are read-only. The bases
    below are the ones the linker chose for the whole image; the check
    later confirms each against the image's symbols. *)

(** The first call reads these twelve objects from the image. *)
Definition hello_start_names : list string :=
  ["glibc_getopt#getopt_data"; "opterr"; "optopt";
   "glibc_getopt#str.146"; "glibc_getopt#str.147"; "glibc_getopt#str.150";
   "hello#parse_options.longopts.64"; "hello#str.65"; "hello#str.66"; "hello#str.67"; "hello#str.68";
   "hello#str.69"]%string.

Definition hello_start_keep (n : name) : bool := existsb (name_eqb n) (map TAtom hello_start_names).

(** The parser expects its private object to hold zeroes, opterr to
    hold 1 and optopt to hold 63 before the first call. This list states
    those values and the three strings at the linked addresses. *)
Definition hello_image_getopt_ps : list (piece * pval) :=
  getopt_start_ps 173680 (gd 173680 173736) 173792 (gd 173792 173800) 173856 (gd 173856 173864)
    174272 (gd 174272 174280) 174304 (gd 174304 174312) 174448 (gd 174448 174456).

(** These are Hello's table, its four names and its option string. The
    loader puts them where it puts them in Hello's own module, because
    Hello's items come first in the link. *)
Definition hello_image_tab_ps : list (piece * pval) :=
  hello_tab_ps 68672 (gd 68672 68832) 69456 69488 69520 69552 69584
    (gd 69456 69472) (gd 69488 69504) (gd 69520 69528) (gd 69552 69560) (gd 69584 69592).

(** HelloGetoptStart.v's table theorem reads exactly this list, table
    first, followed by any extra pieces. *)
Definition hello_start_ps : list (piece * pval) := hello_image_tab_ps ++ hello_image_getopt_ps.

(** A symbol names the writable object at b. *)
Definition lookup_obj (g : list (name * ptr)) (n : string) (b : Z) : bool :=
  match Term.lookup (TAtom n) g with
  | Some p => (ptr_addr p =? b) && match ptr_cap p with Obj c => c =? b | _ => false end
  | None => false
  end.

Lemma lookup_obj_ok g n b : lookup_obj g n b = true -> Term.lookup (TAtom n) g = Some (mkPtr b (Obj b)).
Proof.
  unfold lookup_obj. destruct (Term.lookup (TAtom n) g) as [[a c]|]; [|discriminate]. cbn [ptr_addr ptr_cap].
  destruct c; try (rewrite andb_false_r; discriminate). intros H. apply andb_true_iff in H as [Ha Hc].
  apply Z.eqb_eq in Ha, Hc. subst. reflexivity.
Qed.

(** These are the nine read-only objects with their bases. *)
Definition hello_start_ro : list (string * Z) :=
  [("glibc_getopt#str.146", 174272); ("glibc_getopt#str.147", 174304); ("glibc_getopt#str.150", 174448);
   ("hello#parse_options.longopts.64", 68672); ("hello#str.65", 69456); ("hello#str.66", 69488);
   ("hello#str.67", 69520); ("hello#str.68", 69552); ("hello#str.69", 69584)]%string.

(** The symbols of the image place all twelve objects. *)
Definition hello_start_places (g : list (name * ptr)) : bool :=
  lookup_obj g "glibc_getopt#getopt_data" 173680 && lookup_obj g "opterr" 173792 &&
  lookup_obj g "optopt" 173856 && forallb (fun nb : string * Z => lookup_ro g nb.1 nb.2) hello_start_ro.

(** ## The check on the erased image

    A piece only carries over to the genuine memory when it lies inside
    an object that the copy keeps whole. So the check asks three things
    of the copy: each piece holds its value there, each lies in a kept
    object, and each symbol names the expected object. *)

Definition hello_start_skel : module := Eval vm_compute in erase hello_start_keep hello_image_module.

Lemma hello_start_skel_eq : erase hello_start_keep hello_image_module = hello_start_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_start_kept : module := Eval vm_compute in kept_objects hello_start_keep hello_image_module.

Lemma hello_start_kept_incl : incl hello_start_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_start_keep hello_image_module = hello_start_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_start_check :
  match initial_memory hello_start_skel with
  | Some (g, m') => pieces_ok hello_start_keep hello_start_kept g m' hello_start_ps && hello_start_places g
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The objects in the genuine memory

    A startup proof needs three facts about these objects: the memory
    holds their values, each object is large enough and aligned, and no
    key is claimed twice. The lemmas below give those facts, and the
    last one also covers the fifteen constants of the gettext route. *)

(** The parser reads whole words, so every object must start on an
    aligned address and hold all the words it reads. These bases do. *)
Lemma hello_start_fit :
  let fit b r n := 0 < b /\ b mod 8 = 0 /\ b + n <= r_end r /\ r_end r <= 2 ^ 48 in
  fit 173680 (gd 173680 173736) 56 /\ fit 174272 (gd 174272 174280) 8 /\ fit 174304 (gd 174304 174312) 8 /\
  fit 174448 (gd 174448 174456) 8 /\ fit 68672 (gd 68672 68832) 136 /\ fit 69456 (gd 69456 69472) 16 /\
  fit 69488 (gd 69488 69504) 16 /\ fit 69520 (gd 69520 69528) 8 /\ fit 69552 (gd 69552 69560) 8 /\
  fit 69584 (gd 69584 69592) 8.
Proof. cbv zeta. unfold gd. cbn [r_end]. split_and!; first [lia | reflexivity]. Qed.

(** The loader succeeds on the linked image. Its symbols place the twelve
    objects at the bases above, and its memory holds their pieces with
    distinct keys. In the table, each name slot holds a read-only
    capability to its name, because the loader writes one there. The
    flag slots and the terminator hold no capability. *)
Theorem hello_image_start : exists g m, initial_memory hello_image_module = Some (g, m) /\
  Term.lookup (TAtom "glibc_getopt#getopt_data") g = Some (mkPtr 173680 (Obj 173680)) /\
  Term.lookup (TAtom "opterr") g = Some (mkPtr 173792 (Obj 173792)) /\
  Term.lookup (TAtom "optopt") g = Some (mkPtr 173856 (Obj 173856)) /\
  Forall (fun nb : string * Z => Term.lookup (TAtom nb.1) g = Some (mkPtr nb.2 (Ro nb.2))) hello_start_ro /\
  all_agree m hello_start_ps /\ NoDup hello_start_ps.*1.
Proof.
  destruct hello_image_memory as (g & m & E).
  destruct (image_pieces hello_start_keep hello_start_kept hello_image_module g m hello_start_ps
    hello_start_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_start_check as C. rewrite <- hello_start_skel_eq, E' in C.
  apply andb_true_iff in C as [Cp Cg]. unfold hello_start_places in Cg.
  apply andb_true_iff in Cg as [Cg Cr]. apply andb_true_iff in Cg as [Cg Co].
  apply andb_true_iff in Cg as [Cd Ce].
  exists g, m. split_and!.
  - exact E.
  - exact (lookup_obj_ok _ _ _ Cd).
  - exact (lookup_obj_ok _ _ _ Ce).
  - exact (lookup_obj_ok _ _ _ Co).
  - rewrite forallb_forall in Cr. apply List.Forall_forall. intros nb Hnb. exact (lookup_ro_ok _ _ _ (Cr nb Hnb)).
  - exact (P Cp).
  - apply (NoDup_fmap_1 (fun p => match p with
      | PLive b => 4 * 512 * b | PByte b o => 4 * (512 * b + o) + 1
      | PAux b o => 4 * (512 * b + o) + 2 | _ => 3 end)).
    apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(** These are the bases of the twelve objects, and the bases of the
    fifteen constants. *)
Definition hello_start_bases : list Z :=
  [173680; 173792; 173856; 174272; 174304; 174448; 68672; 69456; 69488; 69520; 69552; 69584].

Definition hello_kept_bases : list Z :=
  [168736; 168672; 164624; hello_domain_base.1] ++ hello_msg_bases.*1 ++ hello_suffix_bases.*1.

(** Every key of a selection names an object at one of its bases, and no
    base of one selection is a base of the other. So the twelve objects
    and the fifteen constants share no key. *)
Lemma hello_start_kept_keys : NoDup (hello_kept_ps ++ hello_start_ps).*1.
Proof.
  assert (H1 : Forall (fun k => piece_id k ∈ hello_kept_bases) hello_kept_ps.*1)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (H2 : Forall (fun k => piece_id k ∈ hello_start_bases) hello_start_ps.*1)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (H3 : Forall (fun b => b ∉ hello_kept_bases) hello_start_bases)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  destruct hello_image_start as (g & m & _ & _ & _ & _ & _ & _ & Hn).
  rewrite fmap_app. apply NoDup_app. split_and!; [exact hello_kept_keys| |exact Hn].
  intros k Hk Hk'. rewrite Forall_forall in H1. rewrite Forall_forall in H2. rewrite Forall_forall in H3.
  exact (H3 _ (H2 _ Hk') (H1 _ Hk)).
Qed.

(** One memory holds both selections. The loader gives the same memory
    each time, so the fifteen constants of HelloImageKept.v and the
    twelve objects here agree with it together. *)
Theorem hello_image_start_kept : exists g m, initial_memory hello_image_module = Some (g, m) /\
  all_agree m (hello_kept_ps ++ hello_start_ps) /\ all_agree m hello_aux_ps /\
  NoDup (hello_kept_ps ++ hello_start_ps).*1.
Proof.
  destruct hello_image_kept as (g & m & E & _ & _ & _ & _ & Ak & Aa & _).
  destruct hello_image_start as (g' & m' & E' & _ & _ & _ & _ & As & _).
  rewrite E in E'. injection E' as <- <-.
  exists g, m. split_and!; [exact E | apply all_agree_app; split; assumption | exact Aa | exact hello_start_kept_keys].
Qed.
