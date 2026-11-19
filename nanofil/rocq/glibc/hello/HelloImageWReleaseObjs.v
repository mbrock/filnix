(** Closing a wide stream checks that neither of the C locale's two
    conversion steps has a finalizer. The same read-only objects that
    glibc reads when it orients the stream hold these two pointers. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap.
From Glibc Require Import ImageObjectPieces HelloImageModule HelloImageLoad
  ImageEraseMem ImagePieces HelloImageWFwideObjs.
Open Scope Z_scope.

(** The pointer at offset 64 of each step has zero address bytes and
    no capability. Neither cell overlaps the library handle at offset
    zero that orientation already owns. *)
Definition hello_wrelease_ps : list (piece * pval) :=
  ptr_ps (img_addr "glibc_wcsmbsload#to_wc") 64 null ++
  ptr_ps (img_addr "glibc_wcsmbsload#to_mb") 64 null.

Lemma hello_wrelease_check :
  match initial_memory hello_wfwide_skel with
  | Some (g, m') => pieces_ok hello_wfwide_keep hello_wfwide_kept g m' hello_wrelease_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The image used for the orientation check already keeps both steps.
    Checking the same objects gives these two cells in the actual
    memory that the loader builds. *)
Lemma hello_wrelease_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_wrelease_ps.
Proof.
  intros E. destruct (image_pieces hello_wfwide_keep hello_wfwide_kept hello_image_module g m hello_wrelease_ps
    hello_wfwide_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_wrelease_check as C. rewrite <- hello_wfwide_skel_eq, E' in C. exact (P C).
Qed.
