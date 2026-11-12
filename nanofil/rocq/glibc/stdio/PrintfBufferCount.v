(** A live printf buffer returns its accumulated count when that count fits
    a nonnegative C int. This proof follows the checked completion body;
    it does not assume that a formatter or a stream write succeeds.

    Separate lifetime shares let the buffer's fields and character storage
    occupy the same allocation. The rule preserves every borrowed field
    and leaves errno in the caller's [[frame]]. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers MemchrLast PrintfStateCode.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The completion rule uses the same runtime and OS interpretation as its caller. *)
Module PrintfBufferCountOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Module MC := MemchrLastOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Read-only completion preserves the caller's concrete world interpretation. *)
Local Instance count_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Adding the buffered characters to the previous count produces a nonnegative C int.
    Shared ownership keeps their allocation alive while both pointers are loaded. *)
Lemma wp_printf_buffer_done_count fr bb breg db dreg bo used written mode dq1 dq2 Φ :
  call_frame glibc___printf_buffer_done [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < db -> 0 <= bo -> 0 <= used -> db + bo + used <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  0 <= written -> written + used < 2 ^ 31 -> mode <> 0 ->
  liveq dq1 bb breg -∗ liveq dq2 db dreg -∗ int_cell bb 32 mode -∗
  pcell bb 0 (mkPtr (db + bo) (Obj db)) -∗
  pcell bb 8 (mkPtr (db + bo + used) (Obj db)) -∗ icell bb 24 written -∗
  ▷ (liveq dq1 bb breg -∗ liveq dq2 db dreg -∗ int_cell bb 32 mode -∗
     pcell bb 0 (mkPtr (db + bo) (Obj db)) -∗
     pcell bb 8 (mkPtr (db + bo + used) (Obj db)) -∗ icell bb 24 written -∗
     Φ (Ret (WInt (written + used)))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hal Hend Hreg Hdb Hbo Hused Hdend Hdreg Hw Htotal Hmode.
  injection Hfr as <-. iIntros "Hl Hd [%Hm Hmode] Hbase Hptr Hwritten HK".
  enter. st. norm.
  iApply (wp_check_read_dq with "Hl");
    [reflexivity | reflexivity | left; reflexivity | ar | ar | ar |].
  iNext. iIntros "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hmode");
    [reflexivity | reflexivity | reflexivity |
     unfold int_bytes;
     rewrite of_bytes_int; [cbn; rewrite !(Z.mod_small mode (2 ^ 32) Hm); reflexivity|exact Hm] |
     left; reflexivity | ar |].
  iNext. iIntros "Hl Hmode". st. brv true. st. st. norm.
  iApply (MC.wp_half_check_read_dq registry (os_wi w0) ge with "Hl");
    [reflexivity | reflexivity | reflexivity | left; reflexivity | ar | ar | lia | ar | ar |].
  iNext. iIntros "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hptr Hd");
    [reflexivity | reflexivity | left; reflexivity | ar | ar | ar |].
  iNext. iIntros "Hl Hptr Hd".
  iApply (MC.wp_half_check_read_dq registry (os_wi w0) ge with "Hl");
    [reflexivity | reflexivity | reflexivity | left; reflexivity | ar | ar | lia | ar | ar |].
  iNext. iIntros "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hbase Hd");
    [reflexivity | reflexivity | left; reflexivity | ar | ar | ar |].
  iNext. iIntros "Hl Hbase Hd".
  st. st. st. st. norm.
  iApply (wp_raw_load_read_dq with "Hl Hwritten");
    [reflexivity | reflexivity | left; reflexivity | ar |].
  iNext. iIntros "Hl Hwritten". norm.
  st. st. st. st. st. st. st. st.
  iApply wp_branch; [vx|iNext].
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    assert (E : (n =? 0) = true) end.
  { replace (db + bo + used - (db + bo)) with used by lia.
    rewrite !(Z.mod_small written (2 ^ 64) ltac:(lia)).
    rewrite !(Z.mod_small used (2 ^ 64) ltac:(lia)).
    rewrite !(Z.mod_small (written + used) (2 ^ 64) ltac:(lia)).
    rewrite !(Z.mod_small (written + used) (2 ^ 32) ltac:(lia)).
    unfold sign_extension.
    rewrite !(Z.mod_small (written + used) (2 ^ 32) ltac:(lia)).
    assert (H31 : (2 ^ 31 <=? written + used) = false) by (apply Z.leb_gt; lia).
    rewrite H31.
    rewrite !(Z.mod_small (written + used) (2 ^ 64) ltac:(lia)).
    assert (H63 : (2 ^ 63 <=? written + used) = false) by (apply Z.leb_gt; lia).
    rewrite H63.
    assert (Hcarry : (written + used <? written) = false) by (apply Z.ltb_ge; lia).
    rewrite Hcarry Z.eqb_refl. cbn.
    rewrite (Z.div_small (written + used) (2 ^ 63) ltac:(lia)). reflexivity. }
  rewrite E. cbn [edge_label]. st. st. norm.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  replace (db + bo + used - (db + bo)) with used by lia. norm.
  iApply ("HK" with "Hl Hd [Hmode] Hbase Hptr Hwritten").
  iSplit; [done|iExact "Hmode"].
Qed.

End rules.
End PrintfBufferCountOn.
