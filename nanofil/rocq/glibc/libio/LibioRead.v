From Glibc Require Import GlibcProgram.
(** Stream readers inspect individual FILE fields or delegate to system-call wrappers.
    This module proves the pending-byte count, error test, stat, and close operations
    over the fields each operation touches.

    A caller must prevent these fields from changing during an operation.
    It does so by owning them through the stream's [[separation-logic]] invariant.
    Narrow streams use mode zero or minus one, and the error test requires locking to be disabled. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsFstat OsRegistry SysCode LibioReadCode FileInv LibioLogic
  SysWrappers.
From Glibc Require FileInv LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
From Glibc Require Import GlibcSpec LibioSpecs.
Import ListNotations.
Open Scope Z_scope.

(** Arithmetic computes on concrete numbers but stays folded on unknown inputs. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).


(** The expression type uses this caller's linked program and registry. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## `c: __fpending` *)

(** The pending-byte query subtracts the stream's write base from its write pointer.
    Both pointers must carry the same capability, and the stream must use narrow mode. *)
Lemma wp_glibc___fpending fr fb freg mode wp wb reg' Φ :
  call_frame glibc___fpending [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (mode = 0 \/ mode = 2 ^ 32 - 1) -> ptr_cap wp = ptr_cap wb ->
  0 <= ptr_addr wp < 2 ^ 64 -> 0 <= ptr_addr wb < 2 ^ 64 ->
  live fb freg -∗ int_cell fb off_mode mode -∗ pcell fb off_write_ptr wp -∗ pcell fb off_write_base wb -∗
  live_cap (ptr_cap wp) reg' -∗
  ▷ (live fb freg -∗ int_cell fb off_mode mode -∗ pcell fb off_write_ptr wp -∗ pcell fb off_write_base wb -∗
     live_cap (ptr_cap wp) reg' -∗ Φ (Ret (WInt ((ptr_addr wp - ptr_addr wb) mod 2 ^ 64)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hfreg Hmode Hcap Hwp Hwb. injection Hfr as <-.
  iIntros "Hl [%Hm Hmode] Hwp Hwb Hc HK". unfold file_size in Hend. step. step. norm. check "Hl".
  load_s32_group "Hl Hmode". step.
  destruct Hmode as [-> | ->]; closed_ints. 1: branch. 2: branch.
  all: step; step; norm; check "Hl";
    (load_pointer "Hl Hwp Hc" by ar);
    iNext; iIntros "Hl Hwp Hc"; step; norm; check "Hl"; rewrite Hcap;
    (load_pointer "Hl Hwb Hc" by ar);
    iNext; iIntros "Hl Hwb Hc"; step; step; step; rewrite -Hcap;
    (iApply wp_ret; [reflexivity | reflexivity |]); iNext; cbn;
    rewrite (Z.mod_small (ptr_addr wp)); [|lia]; rewrite (Z.mod_small (ptr_addr wb)); [|lia];
    rewrite Z.mod_mod; [|lia]; iApply ("HK" with "Hl [Hmode] Hwp Hwb Hc"); (iSplit; [iPureIntro; lia | iExact "Hmode"]).
Qed.

(** ## `c: _IO_ferror` *)

(** The error query returns one when the stream's error flag is set and zero otherwise.
    Its locking macros skip the lock when the need-lock flag is clear. *)
Lemma wp_glibc__IO_ferror fr fb freg fl f2 Φ :
  call_frame glibc__IO_ferror [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 io_need_lock = 0 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗
     Φ (Ret (WInt (if Z.land fl io_err_seen =? 0 then 0 else 1)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hfreg Hnl. injection Hfr as <-.
  iIntros "Hl [%Hf Hfl] [%Hf2 Hfl2] HK". unfold file_size in Hend. step. step. norm. check "Hl".
  load_s32_group "Hl Hfl2". step. step. step. step.
  rewrite flags2_bit7; [|exact Hf2]. unfold io_need_lock in Hnl. rewrite Hnl. branch. step. check "Hl".
  load_s32_group "Hl Hfl". step. step. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  change (32 mod 2 ^ 32) with 32. change (0 mod 2 ^ 32) with 0. rewrite (Z.mod_small fl); [|lia].
  assert (Hb : 0 <= Z.land fl 32 < 2 ^ 32).
  { apply land_lt32; lia. }
  rewrite (Z.mod_small (Z.land fl 32)); [|exact Hb]. unfold io_err_seen.
  destruct (Z.land fl 32 =? 0); cbn [negb];
    (iApply ("HK" with "Hl [Hfl] [Hfl2]"); [iSplit; [done | iExact "Hfl"] | iSplit; [done | iExact "Hfl2"]]).
Qed.

(** ## `c: _IO_file_close` and `c: _IO_file_stat` *)

(** Stat and close call the named system-call wrappers and then return their results.
    The continuation resumes after the wrapper returns its outcome. *)
Ltac resume_ret := iExists _; iSplit; [iPureIntro; reflexivity|]; iNext.

(** Closing a stream passes its descriptor to the close wrapper.
    It returns zero or minus one and preserves ownership of errno's resulting bytes. *)
Lemma wp_glibc__IO_file_close fr fb freg fd eb Φ :
  call_frame glibc__IO_file_close [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  find_fn ge (TAtom "__GI___close_nocancel") = Some (Defined glibc___close_nocancel) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  live fb freg -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live fb freg -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
     Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfn Hfb Hal Hend Hfreg He. injection Hfr as <-.
  iIntros "Hl [%Hfd Hfdb] Herr HK". unfold file_size in Hend. step. step. norm. check "Hl".
  load_s32_group "Hl Hfdb".
  assert (Hclose : Defines ge "__GI___close_nocancel" glibc___close_nocancel) by exact Hfn.
  call_spec with (fd mod 2 ^ 32, eb).
  { split; [apply Z.mod_pos_bound; lia | exact He]. }
  iDestruct "Hpost" as (k) "(%Hout & Herr)". destruct Hout as [-> Hk]. resume_ret.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. rewrite Z.mod_mod; [|lia]. rewrite Z.mod_small; [|lia].
  iApply ("HK" with "[%] Hl [Hfdb] Herr"); [exact Hk | iSplit; [done | iExact "Hfdb"]].
Qed.

(** The stream stat operation passes its descriptor and an owned buffer to the stat wrapper.
    It returns zero or minus one and restores ownership of the buffer's new bytes. *)
Lemma wp_glibc__IO_file_stat fr fb freg fd b reg o eb Φ :
  call_frame glibc__IO_file_stat [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b + o) (Obj b))] = Some fr ->
  find_fn ge (TAtom "__GI___fstat64") = Some (Defined glibc___fstat64) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  0 <= o -> b + o + stat_size <= r_end reg ->
  live fb freg -∗ int_cell fb off_fileno fd -∗ live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live fb freg -∗ int_cell fb off_fileno fd -∗ live b reg -∗
     blk_any b o stat_size -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfn Hfb Hal Hend Hfreg He Hin Ho Hst. injection Hfr as <-.
  iIntros "Hl [%Hfd Hfdb] Hbl Hb Herr HK". unfold file_size in Hend. step. step. norm. check "Hl".
  load_s32_group "Hl Hfdb".
  assert (Hstat : Defines ge "__GI___fstat64" glibc___fstat64) by exact Hfn.
  call_spec with (fd mod 2 ^ 32, b, reg, o, eb).
  { repeat split; try assumption; try (apply Z.mod_pos_bound; lia).
    rewrite Z.mod_small; [exact Hin | lia]. }
  iDestruct "Hpost" as (k) "(%Hout & Hbl & Hb & Herr)". destruct Hout as [-> Hk]. resume_ret.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. rewrite Z.mod_mod; [|lia]. rewrite Z.mod_small; [|lia].
  iApply ("HK" with "[%] Hl [Hfdb] Hbl Hb Herr"); [exact Hk | iSplit; [done | iExact "Hfdb"]].
Qed.

End rules.
