(** The jump table's `c: __finish` of a stream `c: fclose` has closed
    and unlinked: `c: _IO_new_file_finish(fp, 0)` (LibioUnlinkCode.v,
    libio/fileops.c) sees `c: _fileno` -1 and calls
    `c: _IO_default_finish(fp, 0)` (libio/genops.c), which finds no
    buffer, no markers and no backup area, calls `c: _IO_un_link` on
    the unlinked stream, a no-op (LibioUnlink.v's
    [wp_glibc__IO_un_link_unlinked], whose triple is
    [unlink_unlinked_spec]), and returns ([wp_glibc__IO_default_finish_closed],
    [wp_glibc__IO_new_file_finish_closed]). *)

From Glibc Require Import GlibcTactics LibioTactics.
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

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hunl : find_fn ge (TAtom "__GI__IO_un_link") = Some (Defined glibc__IO_un_link)).
Context (Hdf : find_fn ge (TAtom "__GI__IO_default_finish") = Some (Defined glibc__IO_default_finish)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance finish_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_un_link`'s triple on an unlinked stream, as LibioUnlink.v's
    [wp_glibc__IO_un_link_unlinked] states it. *)
Definition unlink_unlinked_spec : Prop := forall fr fb freg fl Φ,
  call_frame glibc__IO_un_link [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_linked = false ->
  live fb freg -∗ int_cell fb off_flags fl -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.

(** [unlink_unlinked_spec] holds. *)
Context (Hunl_spec : unlink_unlinked_spec).

(** `c: _IO_default_finish(fp, 0)` of a closed, unlinked stream: no
    buffer (`c: _IO_buf_base` null), no markers, no backup area
    (`c: _IO_save_base` null), and a lock: nothing changes. *)
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
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hll"). iIntros ([Hl0 Hl48]) "Hll".
  step. step. check "Hl". load_null "Hl" "Hbb". step. step. branch. step. branch.
  step. step. check "Hl". load_null "Hl" "H96". step. step. step. step. step. branch.
  step. step. check "Hl". load_null "Hl" "H80". step. step. branch.
  step. iApply wp_call_bind; [vx | exact Hunl | reflexivity |]. iNext.
  iApply (Hunl_spec with "Hl Hfl"); try close_side.
  iNext. iIntros "Hl Hfl". resume.
  step. check "Hl". load "Hl" "Hlp" "Hll". step. step. branch_as false. step. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hl Hfl Hbb H80 H96 Hlp Hll").
Qed.

(** `c: _IO_new_file_finish(fp, 0)` of a closed, unlinked stream
    (`c: _fileno` -1): [wp_glibc__IO_default_finish_closed]. *)
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
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. check "Hl". load_s32 "Hl" "Hfd". step. branch. step.
  iApply wp_call_bind; [vx | exact Hdf | reflexivity |]. iNext.
  iApply (wp_glibc__IO_default_finish_closed with "Hl Hfl Hbb H80 H96 Hlp Hll"); try close_side.
  iNext. iIntros "Hl Hfl Hbb H80 H96 Hlp Hll". resume. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hl [Hfd] Hfl Hbb H80 H96 Hlp Hll"). iSplit; [done | iExact "Hfd"].
Qed.

End rules.
