(** This file proves the triple of `c: _IO_doallocbuf` (LibioReadCode.v) on an
    unbuffered stream with no buffer: it installs the one byte
    `c: _shortbuf` inside the `c: FILE` itself with
    `c: _IO_setb(fp, fp->_shortbuf, fp->_shortbuf + 1, 0)`. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic SysWrappers
  LibioSetb.
From Glibc Require FileInv LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The genv defines `c: _IO_setb`. *)
Context (Hsetbf : find_fn ge (TAtom "__GI__IO_setb") = Some (Defined glibc__IO_setb)).

Local Instance doallocshort_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_setb` on a stream with no buffer, as LibioSetb.v's
    [wp_glibc__IO_setb] proves it with the old buffer null. *)
Context (Hsetb_null : forall fr fb freg fl oe nb ne a Φ,
  call_frame glibc__IO_setb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl a) -∗ pcell fb off_buf_base nb -∗
     pcell fb off_buf_end ne -∗ Φ RetVoid) -∗
  WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ Φ }}).
(** `c: _IO_doallocbuf(fp)` on an unbuffered stream with no buffer
    makes `c: _shortbuf` its buffer and sets `c: _IO_USER_BUF`. *)
Lemma wp_glibc__IO_doallocbuf_short fr fb freg fl mode oe Φ :
  call_frame glibc__IO_doallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl io_unbuffered <> 0 -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl 0) -∗ int_cell fb off_mode mode -∗
     pcell fb off_buf_base (mkPtr (fb + off_shortbuf) (Obj fb)) -∗
     pcell fb off_buf_end (mkPtr (fb + off_shortbuf + 1) (Obj fb)) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hfreg Hub Hmd. injection Hfr as <-.
  iIntros "Hl Hfl [%Hm Hmb] Hb Hbe HK". unfold file_size in Hend. unfold io_unbuffered in Hub.
  step. step. norm. check "Hl".
  iApply (wp_raw_load_pointer with "Hl Hb [//]"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hb _". step. step. branch.
  step. check "Hl". iDestruct "Hfl" as "[%Hfl Hflb]". load_s32_group "Hl Hflb". step. step.
  assert (Hl2 : 0 <= Z.land fl 2 < 2 ^ 32) by (apply land_lt32; lia). branch_as true.
  step. step. norm. check "Hl". load_s32_group "Hl Hmb". step. step. step. destruct Hmd as [-> | ->]; branch.
  all: step; step; step; norm; iApply wp_call_bind; [vx | exact Hsetbf | reflexivity |]; iNext;
    iApply (Hsetb_null _ fb freg fl oe _ _ 0 with "Hl [$Hflb //] Hb Hbe"); try first [reflexivity | libio_side];
    iNext; iIntros "Hl Hfl Hb Hbe"; iExists _; iSplit; [iPureIntro; reflexivity|]; iNext;
    iApply wp_ret_void; iNext; iApply ("HK" with "Hl Hfl [$Hmb //] Hb Hbe").
  Unshelve. all: exact freg.
Qed.

End rules.
