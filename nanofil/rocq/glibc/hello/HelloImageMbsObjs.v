(** Hello's main converts its greeting to wide characters with gnulib's
    `c: mbsrtowcs`, which calls glibc's `c: mbrtowc` once per character.
    In the C locale that call follows a short path through constant
    data. It reads the character type's conversion data, the C
    locale's table of converters and the step that converts ASCII,
    whose last word points at the converter function. Gnulib's
    `c: hard_locale` also compares the locale's name with "C" and
    "POSIX". No start list holds these objects, so this module lists
    them with what Hello's image holds in each, so that Hello's private
    state can own them from the start.

    Nothing writes these objects, so the private state needs only to
    read them. The list therefore holds the few words that the call
    reads, and it keeps each object alive. Early init already keeps the
    C locale's character data alive, so that object gives only one
    word. A check of the whole image would be slow, so the check reads a
    smaller image that holds only these objects. *)

From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap.
From Glibc Require Import WordString HelloGetoptTable StartImageUnique StartImageCpu HelloImageErase HelloImageEraseMem HelloImagePieces
  HelloImageModule HelloImageLoad HelloStartKept StartImageEarly.
Import ListNotations.
Open Scope Z_scope.

(** This function gives the read-only pointer to the object n. *)
Definition mbs_ro (n : string) : ptr := mkPtr (img_addr n) (Ro (img_addr n)).

(** This piece is the life of the object n. *)
Definition mbs_life (n : string) : piece * pval := (PLive (img_obj n).1, VLive (img_obj n).2).

(** The ASCII step's converter is a function of the image. *)
Definition mbs_ascii_fct : ptr :=
  mkPtr (img_addr "__gconv_transform_ascii_internal") (Fn (TAtom "__gconv_transform_ascii_internal")).

(** To convert a byte, mbrtowc follows four pointers from the C
    locale's character data to the function that converts ASCII. The
    last object on that path also says that no shared library holds the
    function. *)
Definition hello_mbs_conv_ps : list (piece * pval) :=
  ptr_ps (img_addr "_nl_C_LC_CTYPE") 32 (mbs_ro "glibc_C_ctype#lc_ctype_data") ++
  mbs_life "glibc_C_ctype#lc_ctype_data" ::
  ptr_ps (img_addr "glibc_C_ctype#lc_ctype_data") 0 (mbs_ro "__wcsmbs_gconv_fcts_c") ++
  mbs_life "__wcsmbs_gconv_fcts_c" ::
  ptr_ps (img_addr "__wcsmbs_gconv_fcts_c") 0 (mbs_ro "glibc_wcsmbsload#to_wc") ++
  mbs_life "glibc_wcsmbsload#to_wc" ::
  ptr_ps (img_addr "glibc_wcsmbsload#to_wc") 0 null ++
  ptr_ps (img_addr "glibc_wcsmbsload#to_wc") 40 mbs_ascii_fct.

(** These are the two names that `c: hard_locale` compares with. *)
Definition hello_c_text : list Z := [67].
Definition hello_posix_text : list Z := [80; 79; 83; 73; 88].

Definition hello_mbs_ro_ps : list (piece * pval) :=
  lit_ps (img_addr "hard-locale#str.31") (img_obj "hard-locale#str.31").2 (lit_words hello_c_text) ++
  lit_ps (img_addr "hard-locale#str.32") (img_obj "hard-locale#str.32").2 (lit_words hello_posix_text).

(** This is the whole list of the module. *)
Definition hello_mbs_objs_ps : list (piece * pval) := hello_mbs_conv_ps ++ hello_mbs_ro_ps.

(** ## The check on a smaller copy *)

(** The check keeps the objects of the list and every object or
    function that a pointer of the list names. *)
Definition hello_mbs_objs_names : list string :=
  ["_nl_C_LC_CTYPE"; "glibc_C_ctype#lc_ctype_data"; "__wcsmbs_gconv_fcts_c"; "glibc_wcsmbsload#to_wc";
   "__gconv_transform_ascii_internal"; "hard-locale#str.31"; "hard-locale#str.32"]%string.

Definition hello_mbs_objs_keep (n : name) : bool :=
  existsb (name_eqb n) (map TAtom hello_mbs_objs_names).

Definition hello_mbs_objs_skel : module := Eval vm_compute in erase hello_mbs_objs_keep hello_image_module.
Lemma hello_mbs_objs_skel_eq : erase hello_mbs_objs_keep hello_image_module = hello_mbs_objs_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_mbs_objs_kept : module := Eval vm_compute in kept_objects hello_mbs_objs_keep hello_image_module.
Lemma hello_mbs_objs_kept_incl : incl hello_mbs_objs_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_mbs_objs_keep hello_image_module = hello_mbs_objs_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_mbs_objs_check :
  match initial_memory hello_mbs_objs_skel with
  | Some (g, m') => pieces_ok hello_mbs_objs_keep hello_mbs_objs_kept g m' hello_mbs_objs_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The list in the real memory *)

(** Hello starts with these cells as listed, in whatever memory the
    loader builds for it. *)
Lemma hello_mbs_objs_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_mbs_objs_ps.
Proof.
  intros E.
  destruct (image_pieces hello_mbs_objs_keep hello_mbs_objs_kept hello_image_module g m hello_mbs_objs_ps
    hello_mbs_objs_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_mbs_objs_check as C. rewrite <- hello_mbs_objs_skel_eq, E' in C. exact (P C).
Qed.
