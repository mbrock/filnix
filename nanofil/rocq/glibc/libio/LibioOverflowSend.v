(** This file proves block `c: L18` of `c: _IO_new_file_overflow`
    (LibioOverflowBase.v describes the function), reached once the
    stream is putting. An argument of `c: EOF` flushes the pending
    bytes and returns the flush's result; a byte goes to block
    `c: L196` when the buffer is full and to block `c: L198` otherwise
    ([wp_ovf_L18]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv LibioLogic
  SysWrappers LibioOverflowBase.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioOverflowSendOn (R : Runtime) (LG0 : LogicSig R).
Module OB := LibioOverflowBaseOn R LG0.
Import OB OB.SW OB.SW.FI.ML OB.SW.FI.LG OB.SW.FI.L OB.SW.OW OB.SW.FI OB.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The genv defines `c: _IO_new_do_write`. *)
Context (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).

Context (write_ready : Z -> Prop).

Local Instance overflow_send_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_new_do_write` of no bytes, as LibioDoWrite.v proves it
    ([wp_glibc__IO_new_do_write_zero]). *)
Context (Hzero : forall fr fp data Φ,
  call_frame glibc__IO_new_do_write [WPtr fp; WPtr data; WInt 0] = Some fr ->
  ▷ Φ (Ret (WInt 0)) -∗
  WP (ERun fr : sexpr) {{ Φ }}).
(** The flush of the pending bytes, as LibioOverflowCall.v proves it
    ([wp_ovf_do_write]). *)
Context (Hovdw : forall fr fb freg f2 fd eb mode vb vreg bb breg sz k we xs fl tw off Φ,
  call_frame glibc__IO_new_do_write [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr bb (Obj bb)); WInt k] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 < k ->
  write_ready f2 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  ovf_state fb bb breg sz k we xs fl tw off -∗
  ▷ (∀ r we' fl' tw' off', ⌜fw_post k fl r fl'⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz 0 we' xs fl' tw' off' -∗
     Φ (Ret (WInt (if r =? k then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}).
(** Block `c: L198`, as LibioOverflowPut.v proves it ([wp_ovf_L198]). *)
Context (HL198 : forall fb freg ch f2 fd eb mode vb vreg bb breg sz k we xs fl tw off from e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= ch < 256 -> k < sz ->
  write_ready f2 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk47") e = Some (WPtr (mkPtr (fb + off_write_ptr) (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  ovf_state fb bb breg sz k we xs fl tw off -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜(r = ch \/ r = 2 ^ 32 - 1) /\ (fl' = fl \/ fl' = Z.lor fl io_err_seen)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L198") (Some from))) : sexpr) {{ Φ }}).
(** Block `c: L196`, as LibioOverflowFull.v proves it ([wp_ovf_L196]). *)
Context (HL196 : forall fb freg ch f2 fd eb mode vb vreg bb breg sz we xs fl tw off from e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= ch < 256 ->
  write_ready f2 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk47") e = Some (WPtr (mkPtr (fb + off_write_ptr) (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  ovf_state fb bb breg sz sz we xs fl tw off -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜(r = ch \/ r = 2 ^ 32 - 1) /\ (fl' = fl \/ fl' = Z.lor fl io_err_seen)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L196") (Some from))) : sexpr) {{ Φ }}).

(** Block `c: L18`: `c: EOF` flushes and returns the flush's result;
    a byte is stored after a flush when the buffer is full. *)
Lemma wp_ovf_L18 fb freg ch f2 fd eb mode vb vreg bb breg sz k we xs fl tw off from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  write_ready f2 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  ovf_state fb bb breg sz k we xs fl tw off -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜ovf_ret ch r /\ (fl' = fl \/ fl' = Z.lor fl io_err_seen)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L18") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hch Hf2 Hf2r Hfd Happ He Hmd Hv0 Hv2 Hc0.
  iIntros "#Hvt Hl Hfx Hst HK". unfold file_size in Hend.
  iDestruct "Hst" as "(%Hp & Hbl & Hxs & Hfl & Htw & Hoff & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend)".
  destruct Hp as (Hbb & Hbe & Hbreg & Hsz & Hkr & Hxl & Hxr & Hwec & Hwea).
  iDestruct "Hfl" as "[%Hflr Hflb]".
  st. st. destruct Hch as [Hch | ->].
  - assert (Hne : ch <> 2 ^ 32 - 1) by lia. brv true.
    st. st. norm. chk "Hl".
    iApply (wp_raw_load_pointer with "Hl Hwp Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
    iNext. iIntros "Hl Hwp Hbl". st. norm. chk "Hl".
    iApply (wp_raw_load_pointer with "Hl Hbend Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
    iNext. iIntros "Hl Hbend Hbl". st. st. st.
    destruct (Z.eq_dec k sz) as [-> | Hks].
    + brv false.
      iApply (HL196 with "Hvt Hl Hfx [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend]");
        try first [side | lk_prove |
          iApply (ovf_state_intro with "Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); (assumption || lia)].
      iNext. iIntros (r k' we' xs' fl' tw' off' [Hr Hfl']) "Hl Hfx Hst".
      iApply ("HK" with "[%] Hl Hfx Hst"). split; [|exact Hfl'].
      destruct Hr as [-> | ->]; [right; rewrite (proj2 (Z.eqb_neq _ _) Hne); reflexivity | left; reflexivity].
    + brv true. assert (Hks' : k < sz) by lia.
      iApply (HL198 _ _ _ _ _ _ _ _ _ _ _ _ k with "Hvt Hl Hfx [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend]");
        try first [side | lk_prove |
          iApply (ovf_state_intro with "Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); (assumption || lia)].
      iNext. iIntros (r k' we' xs' fl' tw' off' [Hr Hfl']) "Hl Hfx Hst".
      iApply ("HK" with "[%] Hl Hfx Hst"). split; [|exact Hfl'].
      destruct Hr as [-> | ->]; [right; rewrite (proj2 (Z.eqb_neq _ _) Hne); reflexivity | left; reflexivity].
  - br. st. st. norm. chk "Hl".
    iApply (wp_raw_load_pointer with "Hl Hwb Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
    iNext. iIntros "Hl Hwb Hbl". st. norm. chk "Hl".
    iApply (wp_raw_load_pointer with "Hl Hwp Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
    iNext. iIntros "Hl Hwp Hbl".
    iApply (wp_raw_load_pointer with "Hl Hwb Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
    iNext. iIntros "Hl Hwb Hbl". st. st. st. norm.
    replace (bb + k - bb) with k by lia.
    iApply wp_call_bind; [vx | exact Hdwf | reflexivity |]. iNext.
    destruct (Z.eq_dec k 0) as [-> | Hk0].
    + iApply Hzero; [rewrite Z.mod_0_l; [reflexivity | lia] |]. iNext.
      iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
      iApply wp_ret; [reflexivity | vx |]. iNext.
      iApply ("HK" with "[%] Hl Hfx [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend]");
        [split; [right; reflexivity | left; reflexivity] |
         iApply (ovf_state_intro with "Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); (assumption || lia)].
    + iApply (Hovdw with "Hvt Hl Hfx [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend]");
        try first [rewrite Z.mod_small; [reflexivity | lia] | side |
         iApply (ovf_state_intro with "Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); (assumption || lia)].
      iNext. iIntros (r we' fl' tw' off' Hpost) "Hl Hfx Hst".
      iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
      iApply wp_ret; [reflexivity | vx |]. iNext.
      iApply ("HK" with "[%] Hl Hfx Hst"). split; [|destruct Hpost as [[_ ->] | [_ ->]]; tauto].
      destruct (r =? k); [right | left]; reflexivity.
Qed.

End rules.
End LibioOverflowSendOn.
