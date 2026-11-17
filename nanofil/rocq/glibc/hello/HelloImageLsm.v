(** The body of `c: __libc_start_main` itself reads and writes five
    globals of glibc that no call of startup owns: the pointer to the
    auxiliary vector, the secure-mode flag, the debug mask, the flag that
    asks for thread events and the saved stack end. The proof of Hello's
    startup must take them from the memory that the loader builds. This
    module lists them as [StartOwnHiAtexit](../startup/StartOwnHiAtexit.v)
    does for hi_atexit, and shows that Hello's image holds them.

    The whole Hello image is too large to compute, so the check runs on
    a copy of the image that keeps only these five objects, as in
    [HelloImageEarly](HelloImageEarly.v). The addresses come from the
    record [hello_lsm_objs], which is computed from the loader's
    symbols, so a relink changes no line here. *)

From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap.
From Glibc Require Import StartLsmImage StartLsmHello StartImageUnique StartImageCpu HelloImageErase
  HelloImageEraseMem HelloImagePieces HelloImageModule HelloImageLoad.
Import ListNotations.
Open Scope Z_scope.

(** This list gives each of the five globals its region and its bytes
    in Hello's image. Only `c: __libc_enable_secure` starts nonzero. *)
Definition hello_lsm_ps : list (piece * pval) :=
  obj_ps (lo_dx hello_lsm_objs, lo_dxreg hello_lsm_objs) (repeat 0 8%nat) ++
  obj_ps (lo_es hello_lsm_objs, lo_esreg hello_lsm_objs) [1; 0; 0; 0] ++
  obj_ps (lo_dm hello_lsm_objs, lo_dmreg hello_lsm_objs) (repeat 0 4%nat) ++
  obj_ps (lo_re hello_lsm_objs, lo_rereg hello_lsm_objs) [0] ++
  obj_ps (lo_se hello_lsm_objs, lo_sereg hello_lsm_objs) (repeat 0 8%nat).

(** ## The check on a smaller copy

    The copy keeps the five globals and blanks every other object of
    the image. A theorem about the copy then carries the check over to
    the real memory. *)

Definition hello_lsm_keep (n : name) : bool :=
  existsb (name_eqb n) (map TAtom ["_dl_auxv"; "__libc_enable_secure"; "_dl_debug_mask";
    "__nptl_initial_report_events"; "__libc_stack_end"]%string).

Definition hello_lsm_skel : module := Eval vm_compute in erase hello_lsm_keep hello_image_module.
Lemma hello_lsm_skel_eq : erase hello_lsm_keep hello_image_module = hello_lsm_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_lsm_kept : module := Eval vm_compute in kept_objects hello_lsm_keep hello_image_module.
Lemma hello_lsm_kept_incl : incl hello_lsm_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_lsm_keep hello_image_module = hello_lsm_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_lsm_check :
  match initial_memory hello_lsm_skel with
  | Some (g, m') => pieces_ok hello_lsm_keep hello_lsm_kept g m' hello_lsm_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The list in the real memory *)

(** Hello starts with the five globals, in whatever memory the loader
    builds for it. *)
Lemma hello_lsm_agree g m : initial_memory hello_image_module = Some (g, m) -> all_agree m hello_lsm_ps.
Proof.
  intros E.
  destruct (image_pieces hello_lsm_keep hello_lsm_kept hello_image_module g m hello_lsm_ps
    hello_lsm_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_lsm_check as C. rewrite <- hello_lsm_skel_eq, E' in C. exact (P C).
Qed.

(** No piece occurs twice in the list. *)
Lemma hello_lsm_nodup : NoDup hello_lsm_ps.*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.
