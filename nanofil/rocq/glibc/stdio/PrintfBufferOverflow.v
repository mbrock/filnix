(** Printf-buffer completion reports EOVERFLOW when its accumulated character
    count no longer fits a nonnegative C int. This rule follows the checked
    body through that error store and its minus-one return.

    A very large count can wrap to a small value at 64 bits. The carry test
    still rejects it. The function leaves the buffer unchanged and stores
    only the error code. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Interval
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers MemchrLast
  PrintfStateCode PrintfCountBits.
From Glibc Require FileInv LibioLogic MemchrLast OsWorld SysWrappers.
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

(** The errno store preserves the existing world interpretation. *)
Local Instance overflow_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A mathematical count beyond INT_MAX fails even when its low 64 bits look small.
    The caller gets the same buffer resources and errno set to EOVERFLOW. *)
Lemma wp_printf_buffer_done_overflow fr bb breg db dreg bo used written mode dq1 dq2 eb ereg eo prior Φ :
  call_frame glibc___printf_buffer_done [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (eb + eo) (Obj eb)) ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < db -> 0 <= bo -> 0 <= used -> db + bo + used <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  0 <= written < 2 ^ 64 -> 2 ^ 31 <= written + used -> mode <> 0 ->
  0 < eb -> 0 <= eo -> eb + eo + 4 <= r_end ereg -> r_end ereg <= 2 ^ 63 ->
  liveq dq1 bb breg -∗ liveq dq2 db dreg -∗ int_cell bb 32 mode -∗
  pcell bb 0 (mkPtr (db + bo) (Obj db)) -∗
  pcell bb 8 (mkPtr (db + bo + used) (Obj db)) -∗ icell bb 24 written -∗
  live eb ereg -∗ int_cell eb eo prior -∗
  ▷ (liveq dq1 bb breg -∗ liveq dq2 db dreg -∗ int_cell bb 32 mode -∗
     pcell bb 0 (mkPtr (db + bo) (Obj db)) -∗
     pcell bb 8 (mkPtr (db + bo + used) (Obj db)) -∗ icell bb 24 written -∗
     live eb ereg -∗ int_cell eb eo 75 -∗
     Φ (Ret (WInt 4294967295))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Herr Hbb Hal Hend Hreg Hdb Hbo Hused Hdend Hdreg Hw Htotal Hmode Heb Heo Heend Hereg.
  injection Hfr as <-. iIntros "Hl Hd [%Hm Hmode] Hbase Hptr Hwritten Hel [%Hprior Herrno] HK".
  step. step. norm.
  iApply (wp_check_read_dq with "Hl");
    [reflexivity | reflexivity | left; reflexivity | ar | ar | ar |].
  iNext. iIntros "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hmode");
    [reflexivity | reflexivity | reflexivity |
     unfold int_bytes;
     rewrite of_bytes_int; [cbn; rewrite !(Z.mod_small mode (2 ^ 32) Hm); reflexivity|exact Hm] |
     left; reflexivity | ar |].
  iNext. iIntros "Hl Hmode". step. branch_as true. step. step. norm.
  iApply (MemchrLast.wp_half_check_read_dq registry (os_wi w0) ge with "Hl");
    [reflexivity | reflexivity | reflexivity | left; reflexivity | ar | ar | lia | ar | ar |].
  iNext. iIntros "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hptr Hd");
    [reflexivity | reflexivity | left; reflexivity | ar | ar | ar |].
  iNext. iIntros "Hl Hptr Hd".
  iApply (MemchrLast.wp_half_check_read_dq registry (os_wi w0) ge with "Hl");
    [reflexivity | reflexivity | reflexivity | left; reflexivity | ar | ar | lia | ar | ar |].
  iNext. iIntros "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hbase Hd");
    [reflexivity | reflexivity | left; reflexivity | ar | ar | ar |].
  iNext. iIntros "Hl Hbase Hd". step. step. step. step. norm.
  iApply (wp_raw_load_read_dq with "Hl Hwritten");
    [reflexivity | reflexivity | left; reflexivity | ar |].
  iNext. iIntros "Hl Hwritten".
  step. step. step. step. step. step. step. step.
  iApply wp_branch; [GlibcTactics.vx|iNext].
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    assert (E : (n =? 0) = false) end.
  { replace (db + bo + used - (db + bo)) with used by lia.
    rewrite !(Z.mod_small written (2 ^ 64) Hw).
    rewrite !(Z.mod_small used (2 ^ 64) ltac:(lia)).
    rewrite !Z.mod_mod; try lia.
    pose proof (printf_count_overflows written used Hw ltac:(lia) Htotal) as Hoverflow.
    unfold printf_count_overflow in Hoverflow.
    set (total := (written + used) mod 2 ^ 64) in *.
    assert (Hnarrow : sign_extension (2 ^ 32) (2 ^ 31) (total mod 2 ^ 32) =
      sign_extension (2 ^ 32) (2 ^ 31) total).
    { unfold sign_extension. rewrite Z.mod_mod; [reflexivity|lia]. }
    rewrite Hnarrow.
    set (narrowed := sign_extension (2 ^ 32) (2 ^ 31) total) in *.
    rewrite printf_signed64_int; [|apply sign_extension_range; lia].
    change ((63 mod 2 ^ 32) mod 64) with 63.
    destruct (total <? written);
      try change (1 mod 2 ^ 32) with 1;
      try change (1 mod 2 ^ 64) with 1;
      try change (0 mod 2 ^ 32) with 0;
      try change (0 mod 2 ^ 64) with 0;
      destruct (negb (total =? narrowed mod 2 ^ 64));
      destruct (negb (0 =? (narrowed / 2 ^ 63) mod 2 ^ 64));
      destruct (negb (1 =? (narrowed / 2 ^ 63) mod 2 ^ 64));
      cbn in Hoverflow |- *; try discriminate; reflexivity. }
  rewrite E. cbn [edge_label]. step. step. norm. check "Hel".
  iApply (wp_raw_store_w with "Hel Herrno");
    [reflexivity | reflexivity | reflexivity | ar | reflexivity | wi_store |].
  iNext. iIntros "Hel Herrno".
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "Hl Hd [Hmode] Hbase Hptr Hwritten Hel [Herrno]").
  - iSplit; [done|iExact "Hmode"].
  - iSplit; [iPureIntro; lia|iExact "Herrno"].
Qed.

End rules.
