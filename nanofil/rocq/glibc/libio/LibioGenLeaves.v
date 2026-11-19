From Glibc Require Import Unit_libio_genops_os Unit_stdlib_cxa_thread_atexit_impl_os.
From Glibc Require Import GlibcProgram.
(** Process exit runs thread-local destructors and discards stream backup markers.
    This fixture has no registered thread-local destructors, so their function returns immediately.
    A stream with null marker and backup pointers also needs no cleanup writes.

    These proofs preserve the memory each caller lends and supply the contracts
    used by the exit and stream-close paths. *)

From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  LibioCloseItEnd LibioCloseItMid ExitRun.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioCloseSteps SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules_values.
Definition unsave_frame (fb : Z) : frame :=
  mkFrame Unit_libio_genops_os.fn___GI__IO_unsave_markers [(TAtom "v0", WPtr (mkPtr fb (Obj fb)))] [] None
    (Enter (TAtom "start") None).
Lemma unsave_frame_call fb :
  call_frame Unit_libio_genops_os.fn___GI__IO_unsave_markers [WPtr (mkPtr fb (Obj fb))] = Some (unsave_frame fb).
Proof using Type. reflexivity. Qed.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The expression type uses this caller's linked program and registry. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Discarding markers reads the stream's marker and backup pointers.
    When both are null, the function returns without changing either cell. *)
Lemma wp_glibc__IO_unsave_markers fb freg Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg ->
  live fb freg -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  ▷ (live fb freg -∗ pcell fb 80 null -∗ pcell fb 96 null -∗ Φ RetVoid) -∗
  WP (ERun (unsave_frame fb) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfb Hfal Hfend. unfold file_size in Hfend.
  iIntros "Hl H80 H96 HK". unfold unsave_frame.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. check "Hl". load_null "Hl" "H96". step. step. branch.
  step. step. check "Hl". load_null "Hl" "H80". step. step. step. branch.
  step. iApply wp_ret_void. iNext. iApply ("HK" with "Hl H80 H96").
Qed.

(** The marker cleanup proof supplies the contract used when closing a stream. *)
Lemma unsave_spec_holds : LibioCloseItMid.unsave_spec w0 registry ge Unit_libio_genops_os.fn___GI__IO_unsave_markers.
Proof using Type.
  intros fb. exists (unsave_frame fb). split; [apply unsave_frame_call|].
  intros freg Φ Hfb Hfal Hfend. iIntros "Hl H80 H96 HK".
  iApply (wp_glibc__IO_unsave_markers with "Hl H80 H96 HK"); assumption.
Qed.

End rules.

Section dtors.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv).
Context (Hdt : Defines ge "__GI___call_tls_dtors" Unit_stdlib_cxa_thread_atexit_impl_os.fn___GI___call_tls_dtors).
Existing Instance Hdt.

(** The empty destructor function returns immediately and preserves the caller's resources. *)
Lemma dtors_rule_tls (P : iProp Σ) : ⊢ ExitRun.dtors_rule w0 ge P P.
Proof using Hdt.
  iIntros (f e ls lab rest j Ψ) "HP HK".
  iApply wp_call_bind; [reflexivity | exact Hdt | reflexivity |]. iNext.
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply wp_ret_void. iNext. iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HK" with "HP").
Qed.

End dtors.
