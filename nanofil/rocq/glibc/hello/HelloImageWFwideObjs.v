(** Before Hello prints its wide greeting, glibc sets up stdout's two
    character converters. It copies them from a constant table that the
    C locale owns, and it checks that no shared library holds either
    one, so that it need not count references to them. That table and
    the converter back to bytes are constants of Hello's image, and this
    module lists the words of them that the copy reads. The first word of
    the table and the converter to wide characters are already listed
    in [hello_mbs_objs_ps].

    Nothing writes these objects, so the private state needs only to
    read them. A check of the whole image would be slow, so the check
    reads a smaller image that holds only these objects. *)

From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap.
From Glibc Require Import WordString StartImageUnique HelloImageErase HelloImageEraseMem HelloImagePieces
  HelloImageModule HelloImageLoad ImageObjectPieces HelloImageMbsObjs.
Import ListNotations.
Open Scope Z_scope.

(** The table holds one step in each direction. Its second word counts
    the steps to wide characters, its third names the step back to
    bytes, and its fourth counts those steps. That step has no
    shared-library handle. *)
Definition hello_wfwide_ps : list (piece * pval) :=
  cell (img_addr "__wcsmbs_gconv_fcts_c") 8 1 ++
  ptr_ps (img_addr "__wcsmbs_gconv_fcts_c") 16 (mbs_ro "glibc_wcsmbsload#to_mb") ++
  cell (img_addr "__wcsmbs_gconv_fcts_c") 24 1 ++
  mbs_life "glibc_wcsmbsload#to_mb" ::
  ptr_ps (img_addr "glibc_wcsmbsload#to_mb") 0 null.

(** ## The check on a smaller copy *)

Definition hello_wfwide_names : list string :=
  ["__wcsmbs_gconv_fcts_c"; "glibc_wcsmbsload#to_wc"; "glibc_wcsmbsload#to_mb";
   "__gconv_transform_ascii_internal"; "__gconv_transform_internal_ascii"]%string.

Definition hello_wfwide_keep (n : name) : bool :=
  existsb (name_eqb n) (map TAtom hello_wfwide_names).

Definition hello_wfwide_skel : module := Eval vm_compute in erase hello_wfwide_keep hello_image_module.
Lemma hello_wfwide_skel_eq : erase hello_wfwide_keep hello_image_module = hello_wfwide_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_wfwide_kept : module := Eval vm_compute in kept_objects hello_wfwide_keep hello_image_module.
Lemma hello_wfwide_kept_incl : incl hello_wfwide_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_wfwide_keep hello_image_module = hello_wfwide_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_wfwide_check :
  match initial_memory hello_wfwide_skel with
  | Some (g, m') => pieces_ok hello_wfwide_keep hello_wfwide_kept g m' hello_wfwide_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The list in the real memory *)

(** Hello starts with these cells as listed, in whatever memory the
    loader builds for it. *)
Lemma hello_wfwide_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_wfwide_ps.
Proof.
  intros E.
  destruct (image_pieces hello_wfwide_keep hello_wfwide_kept hello_image_module g m hello_wfwide_ps
    hello_wfwide_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_wfwide_check as C. rewrite <- hello_wfwide_skel_eq, E' in C. exact (P C).
Qed.
