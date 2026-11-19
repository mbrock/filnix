From Glibc Require Import Unit_libio_genops_os.
From Glibc Require Import GlibcProgram.
(** An unbuffered stream without a buffer uses its internal one-byte buffer.
    This proof follows `c: _IO_doallocbuf` up to the call that installs that buffer. *)

From Glibc Require Import GlibcTactics OsTactics GlibcSymFunc.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioSetb.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The genv defines `c: _IO_setb`. *)
Context `{Hsetbf : !Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}.

Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The buffer-setting function accepts a stream whose old buffer is null. *)
Context (Hsetb_null : forall fr fb freg fl oe nb ne a Φ,
  call_frame Unit_libio_genops_os.fn___GI__IO_setb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl a) -∗ pcell fb off_buf_base nb -∗
     pcell fb off_buf_end ne -∗ Φ RetVoid) -∗
  WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ Φ }}).
(** `c: _IO_doallocbuf(fp)` on an unbuffered stream with no buffer
    makes `c: _shortbuf` its buffer and sets `c: _IO_USER_BUF`. *)
Lemma wp_glibc__IO_doallocbuf_short fr fb freg fl mode oe Φ :
  call_frame Unit_libio_genops_os.fn___GI__IO_doallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl io_unbuffered <> 0 -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl 0) -∗ int_cell fb off_mode mode -∗
     pcell fb off_buf_base (mkPtr (fb + off_shortbuf) (Obj fb)) -∗
     pcell fb off_buf_end (mkPtr (fb + off_shortbuf + 1) (Obj fb)) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hfreg Hub Hmd. injection Hfr as <-.
  iIntros "Hl Hfl [%Hm Hmb] Hb Hbe HK". unfold file_size in Hend. unfold io_unbuffered in Hub.
  step.
  iAssert (live fb freg ∗ live_cap CNone freg)%I with "[Hl]" as "[Hl Hnull]"; [iFrame; done|].
  iDestruct "Hfl" as "[%Hfl Hflb]".
  unfold null, int_bytes.
  destruct Hmd as [-> | ->].
  all: sym_frun "Hl Hb Hnull Hflb Hmb" (@nil name).
  all: iClear "Hnull"; iApply wp_call_bind; [vx | exact Hsetbf | reflexivity |]; iNext;
    iApply (Hsetb_null _ fb freg fl oe _ _ 0 with "Hl [$Hflb //] Hb Hbe"); try first [reflexivity | libio_side];
    iNext; iIntros "Hl Hfl Hb Hbe"; iExists _; iSplit; [iPureIntro; reflexivity|]; iNext;
    iApply wp_ret_void; iNext; iApply ("HK" with "Hl Hfl [$Hmb //] Hb Hbe").
  Unshelve. all: exact freg.
Qed.

End rules.
