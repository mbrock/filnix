From Glibc Require Import GlibcProgram.
(** This file discharges glibc's final stream cleanup after Hello's exit
    callback has closed stdout and stderr. The remaining stdin stream has
    nothing to flush, so the existing concrete cleanup proof suffices. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import OsWorld OsRegistry LibioCleanupCode LibioCleanupExit
  HelloGlibcDebts HelloGlibcLibsT.
From Glibc Require LibioCleanupExit LibioFlushBody.
From Glibc Require Import Fix.
Open Scope Z_scope.

(** The interface exposes the cleanup triple without its internal modules. *)
Module Type HelloLibsCleanupSig (D : HelloDebtsT).
Import LG0 LG0.L D.
(** Cleanup consumes the resources left by the close callback. *)
Parameter libs_cleanup : forall `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  (w0 : os_world) (ge : genv) (o : hello_objs), hello_link ge o ->
  D.fn_triple w0 ge (TAtom "_IO_cleanup") [] (D.exit_io w0 ge o) (D.ret_int True)%I.
End HelloLibsCleanupSig.

(** The implementation applies glibc's concrete cleanup proof. *)
Module HelloGlibcLibsCleanupOn (D : HelloDebtsT)
  : HelloLibsCleanupSig D.
(** The cleanup proof includes its push, pop and flush callees. *)
Module CL := LibioCleanupExit.
Import LG0 LG0.L D.
Section libs.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs).
(** The call runs with the concrete glibc OS registry. *)
Local Instance cleanup_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** Cleanup consumes the resources left by the close callback. *)
Lemma libs_cleanup : hello_link ge o ->
  D.fn_triple w0 ge (TAtom "_IO_cleanup") [] (D.exit_io w0 ge o) (D.ret_int True)%I.
Proof.
  intros Hk. exists glibc__IO_cleanup. split; [exact (hk_cleanup _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  iIntros "(Hs & Htc & Hls & Hfs) HK".
  iApply (LibioCleanupExit.wp_glibc__IO_cleanup_exit (glibc_program := program_of w0 glibc_os_registry ge) (fun n c H => H) (hk_sys _ _ Hk) fr
    (D.FB.exit_stream false) [ho_in o] (ho_sb o) (ho_sreg o) (ho_fcp o) with "Hs Htc Hls Hfs");
    [exact (hk_push _ _ Hk) |
     exact (hk_pop _ _ Hk) | exact (hk_flush _ _ Hk) |
     apply program_call(LibioFlushBody.flush_body_exit (glibc_program := program_of w0 glibc_os_registry ge));
       [intros n c H; exact H | exact (hk_sys _ _ Hk)] |
     exact Hfr | exact (proj1 (hk_fcp _ _ Hk)) | exact (proj2 (hk_fcp _ _ Hk)) |].
  iNext. iIntros (r Hr) "_ _ _". iApply "HK". iExists r. iSplit; [iPureIntro; split; [reflexivity|lia]|done].
Qed.
End libs.
End HelloGlibcLibsCleanupOn.
