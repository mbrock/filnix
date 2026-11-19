(** The hi_atexit loader supplies the globals and memory pieces that the startup contract requires. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces.
From Glibc Require Import OsStartCalls StartLogic HiAtexitModule HiAtexitGe HiAtexitInitial.
Import ListNotations.
Open Scope Z_scope.
From Glibc Require Import StartLsmImage.

(** This record holds the addresses and regions of hi_atexit, read from
    its symbols and from the memory that the loader builds. *)
Definition hi_lsm_objs : lsm_objs := Eval vm_compute in lsm_objs_in hi_globals (m_regions hi_m0).

(** The regions of the record are the ones that the loader registers at
    those addresses, so a proof that owns the globals at the start owns
    them with these regions. *)
Lemma hi_lsm_regions :
  Forall (fun q => object_region (fst q) (m_regions hi_m0) = Some (snd q))
    [(lo_en hi_lsm_objs, lo_enreg hi_lsm_objs); (lo_dx hi_lsm_objs, lo_dxreg hi_lsm_objs);
     (lo_es hi_lsm_objs, lo_esreg hi_lsm_objs); (lo_dm hi_lsm_objs, lo_dmreg hi_lsm_objs);
     (lo_re hi_lsm_objs, lo_rereg hi_lsm_objs); (lo_se hi_lsm_objs, lo_sereg hi_lsm_objs)].
Proof. repeat constructor; vm_compute; reflexivity. Qed.

(** A proof of the startup of hi_atexit can call the body of
    `c: __libc_start_main` without checking the image again, because
    the image meets every pure premise of that proof. *)
Lemma hi_lsm_image_ok : lsm_image_ok hge hi_lsm_objs.
Proof.
  unfold lsm_image_ok, os_ext.
  repeat split; first [vm_compute; reflexivity | vm_compute; intro; discriminate].
Qed.
