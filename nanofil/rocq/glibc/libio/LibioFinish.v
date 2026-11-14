From Glibc Require Import GlibcProgram.
(** Finishing a closed, unlinked stream leaves its memory unchanged.
    The file-specific routine sees that the file descriptor is -1 and
    calls the default routine. That routine finds no buffer, markers,
    or backup area to release. Its unlink call does nothing because
    the stream is already unlinked.

    These proofs preserve the caller's [[separation-logic|ownership]] of the stream and
    its lock. The default routine uses one symbolic run for the
    blocks preceding the unlink call, then applies the callee's contract. *)

From Glibc Require Import GlibcTactics LibioTactics GlibcSymFunc.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioUnlinkCode FileInv LibioLogic SysWrappers
  LibioCloseSteps.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Import ProgramAbbreviations.
Section rules_values.
Context {hlc : has_lc}
  {Σ : gFunctors}
  {invGS_gen0 : invGS_gen hlc Σ}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (w0 : os_world)
  (registry : name -> option (contract os_world))
  (ge : genv).
Existing Instance invGS_gen0.
Existing Instance gen_heapGS0.
Local Instance finish_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Definition unlink_unlinked_spec : Prop := forall fr fb freg fl Φ,
  call_frame glibc__IO_un_link [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_linked = false ->
  live fb freg -∗ int_cell fb off_flags fl -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hunl : !Defines ge "__GI__IO_un_link" glibc__IO_un_link}.
Context `{Hdf : !Defines ge "__GI__IO_default_finish" glibc__IO_default_finish}.


(** The execution goal uses the language selected by the program context. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The caller supplies the unlink contract for an already unlinked stream. *)
Context (Hunl_spec : (unlink_unlinked_spec w0 registry ge)).

(** The default finish routine preserves a closed stream whose buffer,
    markers, and backup area are null. The stream still owns its lock. *)
Lemma wp_glibc__IO_default_finish_closed fr fb freg fl lb lbreg Φ :
  call_frame glibc__IO_default_finish [WPtr (mkPtr fb (Obj fb)); WInt 0] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_linked = false -> 0 < lb -> lb + 16 <= r_end lbreg ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb 80 null -∗
  pcell fb 96 null -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗ live lb lbreg -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb 80 null -∗
     pcell fb 96 null -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗ live lb lbreg -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hfal Hfend Hfreg Hfl Hlnk Hlb Hlbend. injection Hfr as <-. unfold file_size in Hfend.
  iIntros "Hl Hfl Hbb H80 H96 Hlp Hll HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hll"). iIntros ([Hl0 Hl48]) "Hll".
  step.
  iAssert (live fb freg ∗ live_cap CNone freg)%I with "[Hl]" as "[Hl Hnull]"; [iFrame; done|].
  unfold null.
  sym_frun "Hl Hbb H96 H80 Hnull" (@nil name).
  iClear "Hnull".
  iApply wp_call_bind; [vx | exact Hunl | reflexivity |]. iNext.
  iApply (Hunl_spec with "Hl Hfl"); try close_side.
  iNext. iIntros "Hl Hfl". resume.
  step. check "Hl". load "Hl" "Hlp" "Hll". step. step. branch_as false. step. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hl Hfl Hbb H80 H96 Hlp Hll").
Qed.

(** The file-specific finish routine delegates to the default routine
    when the stream's file descriptor is -1. *)
Lemma wp_glibc__IO_new_file_finish_closed fr fb freg fl lb lbreg Φ :
  call_frame glibc__IO_new_file_finish [WPtr (mkPtr fb (Obj fb)); WInt 0] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_linked = false -> 0 < lb -> lb + 16 <= r_end lbreg ->
  live fb freg -∗ int_cell fb off_fileno (2 ^ 32 - 1) -∗ int_cell fb off_flags fl -∗
  pcell fb off_buf_base null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  pcell fb off_lock (mkPtr lb (Obj lb)) -∗ live lb lbreg -∗
  ▷ (live fb freg -∗ int_cell fb off_fileno (2 ^ 32 - 1) -∗ int_cell fb off_flags fl -∗
     pcell fb off_buf_base null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
     pcell fb off_lock (mkPtr lb (Obj lb)) -∗ live lb lbreg -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hfal Hfend Hfreg Hfl Hlnk Hlb Hlbend. injection Hfr as <-. unfold file_size in Hfend.
  iIntros "Hl [%Hfd Hfd] Hfl Hbb H80 H96 Hlp Hll HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. check "Hl". load_s32 "Hl" "Hfd". step. branch. step.
  iApply wp_call_bind; [vx | exact Hdf | reflexivity |]. iNext.
  iApply (wp_glibc__IO_default_finish_closed with "Hl Hfl Hbb H80 H96 Hlp Hll"); try close_side.
  iNext. iIntros "Hl Hfl Hbb H80 H96 Hlp Hll". resume. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hl [Hfd] Hfl Hbb H80 H96 Hlp Hll"). iSplit; [done | iExact "Hfd"].
Qed.

End rules.
