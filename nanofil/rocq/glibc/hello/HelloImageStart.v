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
From Glibc Require Import GetoptInitial ImageData WordString HelloGetoptTable.
From Glibc Require Import ImageErase ImageEraseMem ImagePieces HelloImageModule HelloImageLoad
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
  getopt_start_ps (img_a "glibc_getopt#getopt_data") (img_gd "glibc_getopt#getopt_data") (img_a "opterr") (img_gd "opterr") (img_a "optopt") (img_gd "optopt")
    (img_a "glibc_getopt#str.146") (img_gd "glibc_getopt#str.146") (img_a "glibc_getopt#str.147") (img_gd "glibc_getopt#str.147") (img_a "glibc_getopt#str.150") (img_gd "glibc_getopt#str.150").

(** These are Hello's table, its four names and its option string. The
    loader puts them where it puts them in Hello's own module, because
    Hello's items come first in the link. *)
Definition hello_image_tab_ps : list (piece * pval) :=
  hello_tab_ps (img_a "hello#parse_options.longopts.64") (img_gd "hello#parse_options.longopts.64") (img_a "hello#str.65") (img_a "hello#str.66") (img_a "hello#str.67") (img_a "hello#str.68") (img_a "hello#str.69")
    (img_gd "hello#str.65") (img_gd "hello#str.66") (img_gd "hello#str.67") (img_gd "hello#str.68") (img_gd "hello#str.69").

(** HelloGetoptStart.v's table theorem reads exactly this list, table
    first, followed by any extra pieces. *)
Definition hello_start_ps : list (piece * pval) := hello_image_tab_ps ++ hello_image_getopt_ps.

(** These are the nine read-only objects with their bases. *)
Definition hello_start_ro : list (string * Z) :=
  [(img_sym "glibc_getopt#str.146"); (img_sym "glibc_getopt#str.147"); (img_sym "glibc_getopt#str.150");
   (img_sym "hello#parse_options.longopts.64"); (img_sym "hello#str.65"); (img_sym "hello#str.66");
   (img_sym "hello#str.67"); (img_sym "hello#str.68"); (img_sym "hello#str.69")]%string.

(** The symbols of the image place all twelve objects. *)
Definition hello_start_places (g : list (name * ptr)) : bool :=
  lookup_obj g "glibc_getopt#getopt_data" (img_a "glibc_getopt#getopt_data") && lookup_obj g "opterr" (img_a "opterr") &&
  lookup_obj g "optopt" (img_a "optopt") && forallb (fun nb : string * Z => lookup_ro g nb.1 nb.2) hello_start_ro.

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
  fit (img_a "glibc_getopt#getopt_data") (img_gd "glibc_getopt#getopt_data") 56 /\ fit (img_a "glibc_getopt#str.146") (img_gd "glibc_getopt#str.146") 8 /\ fit (img_a "glibc_getopt#str.147") (img_gd "glibc_getopt#str.147") 8 /\
  fit (img_a "glibc_getopt#str.150") (img_gd "glibc_getopt#str.150") 8 /\ fit (img_a "hello#parse_options.longopts.64") (img_gd "hello#parse_options.longopts.64") 136 /\ fit (img_a "hello#str.65") (img_gd "hello#str.65") 16 /\
  fit (img_a "hello#str.66") (img_gd "hello#str.66") 16 /\ fit (img_a "hello#str.67") (img_gd "hello#str.67") 8 /\ fit (img_a "hello#str.68") (img_gd "hello#str.68") 8 /\
  fit (img_a "hello#str.69") (img_gd "hello#str.69") 8.
Proof. cbv zeta. unfold gd. cbn [r_end]. split_and!; first [lia | reflexivity]. Qed.

(** The loader succeeds on the linked image. Its symbols place the twelve
    objects at the bases above, and its memory holds their pieces with
    distinct keys. In the table, each name slot holds a read-only
    capability to its name, because the loader writes one there. The
    flag slots and the terminator hold no capability. *)
Theorem hello_image_start : exists g m, initial_memory hello_image_module = Some (g, m) /\
  Term.lookup (TAtom "glibc_getopt#getopt_data") g = Some (mkPtr (img_a "glibc_getopt#getopt_data") (Obj (img_a "glibc_getopt#getopt_data"))) /\
  Term.lookup (TAtom "opterr") g = Some (mkPtr (img_a "opterr") (Obj (img_a "opterr"))) /\
  Term.lookup (TAtom "optopt") g = Some (mkPtr (img_a "optopt") (Obj (img_a "optopt"))) /\
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
  [(img_a "glibc_getopt#getopt_data"); (img_a "opterr"); (img_a "optopt"); (img_a "glibc_getopt#str.146"); (img_a "glibc_getopt#str.147"); (img_a "glibc_getopt#str.150"); (img_a "hello#parse_options.longopts.64"); (img_a "hello#str.65"); (img_a "hello#str.66"); (img_a "hello#str.67"); (img_a "hello#str.68"); (img_a "hello#str.69")].

Definition hello_kept_bases : list Z :=
  [(img_a "_nl_category_names"); (img_a "_nl_category_name_idxs"); (img_a "_nl_C_name"); hello_domain_base.1] ++ hello_msg_bases.*1 ++ hello_suffix_bases.*1.

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
