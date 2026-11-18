(** Hello's main calls `c: setlocale (LC_ALL, "")` first. In the C
    locale that call copies constant data into the global locale, so
    the proof must be able to read that data. Another module lists the
    cells that setlocale writes, and this module lists the constants
    that it reads, so that Hello's private state can own them from the
    start.

    Setlocale reads the C locale object `c: _nl_C_locobj` and copies it
    into the global locale. It reads the use count of each category's C
    data and the 32-bit character tables. It also reads its table of
    updates, the name "POSIX", and the length and offset of each
    category's name. Nothing writes these objects. The list keeps each
    object alive unless early init or getopt's list already does. A
    check of the whole image would be slow, so the check reads a smaller
    image that holds only these objects. *)

From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap StringLogic.
From Glibc Require Import WordString HelloGetoptTable StartImageUnique StartImageCpu HelloImageErase HelloImageEraseMem HelloImagePieces
  HelloImageModule HelloImageLoad HelloStartKept StartImageEarly HelloImageLocaleObjs.
Import ListNotations.
Open Scope Z_scope.

(** This piece is the life of the object n. *)
Definition cl_life (n : string) : piece * pval := (PLive (img_obj n).1, VLive (img_obj n).2).

(** The C locale object has the global locale's layout: one pointer per
    category, with none for LC_ALL, and three pointers into the
    character tables. *)
Definition hello_c_locobj_ps : list (piece * pval) :=
  let lb := img_addr "_nl_C_locobj" in
  cl_life "_nl_C_locobj" ::
  ptr_ps lb 0 (ro_at "_nl_C_LC_CTYPE" 0) ++
  List.concat (map (fun c => ptr_ps lb (8 * c.1) (ro_at c.2 0)) hello_locale_cats) ++
  ptr_ps lb 48 null ++
  ptr_ps lb 104 (ro_at "_nl_C_LC_CTYPE_class" 256) ++
  ptr_ps lb 112 (ro_at "_nl_C_LC_CTYPE_tolower" 512) ++
  ptr_ps lb 120 (ro_at "_nl_C_LC_CTYPE_toupper" 512).

(** Each category's C data carries a use count at offset 40, and its
    value marks the data as never freed. Setlocale reads it before it
    switches a category. Early init already keeps the character type's
    data alive, so this list keeps the other eleven alive. *)
Definition cl_undeletable : list Z := [255; 255; 255; 255].

Definition hello_c_counts_ps : list (piece * pval) :=
  byte_ps (img_addr "_nl_C_LC_CTYPE") 40 cl_undeletable ++
  List.concat (map (fun c => cl_life c.2 :: byte_ps (img_addr c.2) 40 cl_undeletable) hello_locale_cats).

(** The character type's update reads the 32-bit class table and the
    32-bit case tables from the C data. *)
Definition hello_c_ctype32_ps : list (piece * pval) :=
  let cc := img_addr "_nl_C_LC_CTYPE" in
  ptr_ps cc 96 (ro_at "_nl_C_LC_CTYPE_class32" 0) ++
  ptr_ps cc 176 (ro_at "_nl_C_LC_CTYPE_toupper" 512) ++
  ptr_ps cc 184 (ro_at "_nl_C_LC_CTYPE_tolower" 512) ++
  [cl_life "_nl_C_LC_CTYPE_class32"].

(** Only the character type has an update to run after a change. *)
Definition hello_c_postload_ps : list (piece * pval) :=
  let pb := img_addr "glibc_setlocale#_nl_category_postload" in
  cl_life "glibc_setlocale#_nl_category_postload" ::
  ptr_ps pb 0 (mkPtr (img_addr "_nl_postload_ctype") (Fn (TAtom "_nl_postload_ctype"))) ++
  List.concat (map (fun i => ptr_ps pb (8 * i) null) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]).

(** Setlocale compares a requested name with "POSIX", and it finds
    each category's name by its length and offset. Getopt's list already
    holds the offset of the messages' name. *)
Definition hello_posix_name_text : list Z := [80; 79; 83; 73; 88].
Definition hello_name_sizes : list Z := [8; 10; 7; 10; 11; 11; 6; 8; 7; 10; 12; 14; 17].

Definition hello_c_names_ps : list (piece * pval) :=
  lit_ps (img_addr "_nl_POSIX_name") (img_obj "_nl_POSIX_name").2 (lit_words hello_posix_name_text) ++
  cl_life "_nl_category_name_sizes" :: byte_ps (img_addr "_nl_category_name_sizes") 0 hello_name_sizes ++
  byte_ps (img_addr "_nl_category_name_idxs") 0 [11; 32; 43; 0; 20] ++
  byte_ps (img_addr "_nl_category_name_idxs") 6 [0; 63; 72; 80; 91; 104; 119].

(** This is the whole list of the module. *)
Definition hello_clocale_objs_ps : list (piece * pval) :=
  hello_c_locobj_ps ++ hello_c_counts_ps ++ hello_c_ctype32_ps ++ hello_c_postload_ps ++ hello_c_names_ps.

(** ## The check on a smaller copy *)

(** The check keeps the objects of the list and every object or
    function that a pointer of the list names. *)
Definition hello_clocale_objs_names : list string :=
  ["_nl_C_locobj"; "_nl_C_LC_CTYPE"; "_nl_C_LC_CTYPE_class"; "_nl_C_LC_CTYPE_tolower"; "_nl_C_LC_CTYPE_toupper";
   "_nl_C_LC_CTYPE_class32"; "glibc_setlocale#_nl_category_postload"; "_nl_postload_ctype"; "_nl_POSIX_name";
   "_nl_category_name_sizes"; "_nl_category_name_idxs"]%string ++ map snd hello_locale_cats.

Definition hello_clocale_objs_keep (n : name) : bool :=
  existsb (name_eqb n) (map TAtom hello_clocale_objs_names).

Definition hello_clocale_objs_skel : module := Eval vm_compute in erase hello_clocale_objs_keep hello_image_module.
Lemma hello_clocale_objs_skel_eq : erase hello_clocale_objs_keep hello_image_module = hello_clocale_objs_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_clocale_objs_kept : module :=
  Eval vm_compute in kept_objects hello_clocale_objs_keep hello_image_module.
Lemma hello_clocale_objs_kept_incl : incl hello_clocale_objs_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_clocale_objs_keep hello_image_module = hello_clocale_objs_kept)
    by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_clocale_objs_check :
  match initial_memory hello_clocale_objs_skel with
  | Some (g, m') => pieces_ok hello_clocale_objs_keep hello_clocale_objs_kept g m' hello_clocale_objs_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The list in the real memory *)

(** Hello starts with these cells as listed, in whatever memory the
    loader builds for it. *)
Lemma hello_clocale_objs_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_clocale_objs_ps.
Proof.
  intros E.
  destruct (image_pieces hello_clocale_objs_keep hello_clocale_objs_kept hello_image_module g m hello_clocale_objs_ps
    hello_clocale_objs_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_clocale_objs_check as C. rewrite <- hello_clocale_objs_skel_eq, E' in C. exact (P C).
Qed.
