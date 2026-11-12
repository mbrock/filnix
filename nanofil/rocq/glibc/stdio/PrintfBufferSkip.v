(** A failed printf buffer stops further writes and flushes before touching
    its character storage. A zero-length write also returns without reading
    its source or the buffer pointers, even when the buffer has not failed.

    These rules follow the checked bodies and preserve the mode field.
    Stream ownership, errno and character storage remain in the caller's
    [[frame]]; no successful output or stream-call contract is assumed. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers PrintfBufferIoCode.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The rules use the caller's runtime and concrete OS interpretation. *)
Module PrintfBufferSkipOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Buffer reads leave the concrete world interpretation unchanged. *)
Local Instance skip_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Failure or an empty input prevents the write loop from touching either
    character allocation. The source pointer therefore needs no ownership. *)
Lemma wp_printf_buffer_write_skip fr bb breg src count mode Φ :
  call_frame glibc___printf_buffer_write
    [WPtr (mkPtr bb (Obj bb)); WPtr src; WInt count] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  (mode = 0 \/ count = 0) ->
  live bb breg -∗ int_cell bb 32 mode -∗
  ▷ (live bb breg -∗ int_cell bb 32 mode -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hal Hend Hreg Hskip. injection Hfr as <-.
  iIntros "Hl [%Hm Hmode] HK". enter. st. norm. chk "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hmode");
    [reflexivity | reflexivity | reflexivity |
     unfold int_bytes; rewrite of_bytes_int;
       [cbn; rewrite !(Z.mod_small mode (2 ^ 32) Hm); reflexivity|exact Hm] |
     left; reflexivity | ar |].
  iNext. iIntros "Hl Hmode". st.
  destruct (Z.eq_dec mode 0) as [->|Hmode].
  - closed_ints. br. st. iApply wp_ret_void. iNext.
    iApply ("HK" with "Hl [Hmode]"). iSplit; [done|iExact "Hmode"].
  - assert (count = 0) as -> by tauto.
    brv true. st. st. closed_ints. br. st. iApply wp_ret_void. iNext.
    iApply ("HK" with "Hl [Hmode]"). iSplit; [done|iExact "Hmode"].
Qed.

(** Flushing an already failed buffer reports false without dispatching to
    a stream or inspecting any buffer pointer. *)
Lemma wp_printf_buffer_flush_failed fr bb breg Φ :
  call_frame glibc___printf_buffer_flush [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  live bb breg -∗ int_cell bb 32 0 -∗
  ▷ (live bb breg -∗ int_cell bb 32 0 -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hal Hend Hreg. injection Hfr as <-.
  iIntros "Hl [%Hm Hmode] HK". enter. st. norm. chk "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hmode");
    [reflexivity | reflexivity | reflexivity | cbn; reflexivity |
     left; reflexivity | ar |].
  iNext. iIntros "Hl Hmode". st. closed_ints. br. st.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "Hl [Hmode]"). iSplit; [iPureIntro; lia|iExact "Hmode"].
Qed.

End rules.
End PrintfBufferSkipOn.
