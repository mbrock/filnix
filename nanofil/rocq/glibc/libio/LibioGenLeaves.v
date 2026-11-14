(** Two leaves of user glibc's genops unit (LibioGenCode.v) that the
    exit path calls: `c: __call_tls_dtors`, which `c: exit` runs before
    the atexit handlers, and `c: _IO_unsave_markers`, which
    `c: _IO_file_close_it` runs before it closes a stream.

    In this build `c: __call_tls_dtors` is one block that returns at
    once, since no thread-local destructor can be registered without
    `c: __cxa_thread_atexit_impl`'s list, which the fixture keeps empty.
    So it is ExitRun.v's [dtors_rule] from any resource to itself
    ([dtors_rule_tls]).

    `c: _IO_unsave_markers(fp)` reads `c: fp->_markers` (offset 96)
    and `c: fp->_IO_backup_base` (offset 80, the field glibc 2.44's
    `c: _IO_have_backup` tests). When both are null it writes nothing
    and calls nothing ([wp_glibc__IO_unsave_markers]), which is
    LibioCloseItMid.v's [unsave_spec] for it ([unsave_spec_holds]). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  LibioGenCode LibioCloseItEnd LibioCloseItMid ExitRun.
From Glibc Require ExitRun FileInv LibioCloseItMid LibioCloseSteps LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance gen_leaves_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The frame of `c: _IO_unsave_markers(fp)` for the stream fb. *)
Definition unsave_frame (fb : Z) : frame :=
  mkFrame glibc__IO_unsave_markers [(TAtom "v0", WPtr (mkPtr fb (Obj fb)))] [] None
    (Enter (TAtom "start") None).

(** That is the frame the call of `c: _IO_unsave_markers` with fp builds. *)
Lemma unsave_frame_call fb :
  call_frame glibc__IO_unsave_markers [WPtr (mkPtr fb (Obj fb))] = Some (unsave_frame fb).
Proof. reflexivity. Qed.

(** `c: _IO_unsave_markers(fp)` of the 8-aligned stream fb, whose
    224 bytes its life covers, with `c: _markers` and
    `c: _IO_backup_base` null: it reads both cells and returns,
    writing nothing. *)
Lemma wp_glibc__IO_unsave_markers fb freg Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg ->
  live fb freg -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  ▷ (live fb freg -∗ pcell fb 80 null -∗ pcell fb 96 null -∗ Φ RetVoid) -∗
  WP (ERun (unsave_frame fb) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hfal Hfend. unfold file_size in Hfend.
  iIntros "Hl H80 H96 HK". unfold unsave_frame.
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. check "Hl". load_null "Hl" "H96". step. step. branch.
  step. step. check "Hl". load_null "Hl" "H80". step. step. step. branch.
  step. iApply wp_ret_void. iNext. iApply ("HK" with "Hl H80 H96").
Qed.

(** LibioCloseItMid.v's [unsave_spec] holds of glibc's
    `c: _IO_unsave_markers`. *)
Lemma unsave_spec_holds : LibioCloseItMid.unsave_spec w0 registry ge glibc__IO_unsave_markers.
Proof.
  intros fb. exists (unsave_frame fb). split; [apply unsave_frame_call|].
  intros freg Φ Hfb Hfal Hfend. iIntros "Hl H80 H96 HK".
  iApply (wp_glibc__IO_unsave_markers with "Hl H80 H96 HK"); assumption.
Qed.

End rules.

Section dtors.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv).
Context (Hdt : find_fn ge (TAtom "__GI___call_tls_dtors") = Some (Defined glibc___call_tls_dtors)).

(** `c: __call_tls_dtors ()` returns at once: ExitRun.v's
    [dtors_rule] holds from any resource P to itself. *)
Lemma dtors_rule_tls (P : iProp Σ) : ⊢ ExitRun.dtors_rule w0 ge P P.
Proof.
  iIntros (f e ls lab rest j Ψ) "HP HK".
  iApply wp_call_bind; [reflexivity | exact Hdt | reflexivity |]. iNext.
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply wp_ret_void. iNext. iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HK" with "HP").
Qed.

End dtors.
