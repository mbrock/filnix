(** The hi_atexit loader supplies the globals and memory pieces that the startup contract requires. *)

From Glibc Require Import HiAtexitModule.
From Glibc Require Import ImageObjectPieces.
From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Semantics Pieces Heap Runtime Logic StringLogic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld OsRegistry StartCtors StartTunableGetValSpec StartCtypeInitSpec
  StartPtmallocInitSpec StartEarlyInitSpec StartImageUnique.
From Glibc Require Import ImageErase ImageEraseMem ImagePieces HiAtexitInitial HiAtexitImage HiAtexitGe.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.
From Glibc Require Import StartImageEarly.

Definition hi_ei_objs : ei_objs := Eval vm_compute in ei_objs_in hi_globals hi_image_regions.
Definition hi_ct_objs : ct_objs := Eval vm_compute in ct_objs_in hi_globals hi_image_regions.
Definition hi_pm_objs : pm_objs := Eval vm_compute in pm_objs_in hi_globals hi_image_regions.
Definition hi_runner_objs := Eval vm_compute in runner_objs_in hi_globals hi_image_regions.

Definition hi_early_ps : list (piece * pval) := early_ps hi_ei_objs hi_pm_objs hi_ct_objs.
Definition hi_runner_ps : list (piece * pval) := runner_ps hi_runner_objs.

(** A check that keeps objects by name, rather than by the bases of its
    pieces, avoids collecting and deduplicating those bases. *)
Lemma hi_m0_pieces_by keep ps :
  pieces_ok keep hi_module hi_globals (hi_erased keep) ps = true -> all_agree hi_m0 ps.
Proof.
  destruct (image_pieces keep hi_module hi_module hi_globals hi_m0 ps (incl_refl _)
    hi_initial hi_module_names hi_module_zeros) as (m' & E & _ & H).
  unfold hi_erased. rewrite E. exact H.
Qed.

(** The linked hi_atexit program starts with both lists, and neither
    list names a piece twice. *)
Lemma hi_early_agree : all_agree hi_m0 hi_early_ps.
Proof.
  unfold hi_early_ps, early_ps. apply all_agree_app. split.
  - apply (hi_m0_pieces_by early_keep). vm_cast_no_check (eq_refl true).
  - apply (hi_m0_pieces_by arena_keep). vm_cast_no_check (eq_refl true).
Qed.

Lemma hi_early_nodup : NoDup hi_early_ps.*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.

Lemma hi_runner_agree : all_agree hi_m0 hi_runner_ps.
Proof. apply (hi_m0_pieces_by early_keep). vm_cast_no_check (eq_refl true). Qed.

Lemma hi_runner_nodup : NoDup hi_runner_ps.*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.

Section hi.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Local Notation hi_program := (program_of w0 glibc_os_registry hge).

(** The program names the objects of early init where the records say,
    and each object is aligned and large enough. The allocator's
    `c: errno` must be the world's. *)
Lemma hi_early_ok :
  ow_errno w0 = Some (mkPtr (pm_eb hi_pm_objs) (Obj (pm_eb hi_pm_objs))) ->
  ei_ok (glibc_program := hi_program) hi_ei_objs /\ ct_ok (glibc_program := hi_program) hi_ct_objs /\
  pm_ok (glibc_program := hi_program) hi_pm_objs /\
  tunable_slot_ok (glibc_program := hi_program) (pm_tl hi_pm_objs) (pm_tlreg hi_pm_objs) 27.
Proof using Type.
  intros Herr. unfold ei_ok, ct_ok, pm_ok, tunable_slot_ok, program_ge, program_world. cbn [program_of].
  cbv [pm_size_ids pm_int_ids app].
  repeat match goal with
  | |- _ /\ _ => split
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor
  end.
  all: first [exact Herr | vm_compute; reflexivity | vm_compute; congruence].
Qed.

(** The program names the runner's flag and table where the record
    says, and both fit. *)
Lemma hi_runner_ok :
  lookup ctor_flag_name (ge_globals hge) = Some (mkPtr hi_runner_objs.1.1 (Obj hi_runner_objs.1.1)) /\
  lookup ctor_table_name (ge_globals hge) = Some (mkPtr hi_runner_objs.2.1 (Ro hi_runner_objs.2.1)) /\
  hi_runner_objs.1.1 + 1 <= r_end hi_runner_objs.1.2 /\ hi_runner_objs.2.1 mod 8 = 0 /\
  hi_runner_objs.2.1 + ctor_table_size 3 <= r_end hi_runner_objs.2.2.
Proof using Type. repeat split; first [vm_compute; reflexivity | vm_compute; congruence]. Qed.

End hi.
