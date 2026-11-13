(** This file proves block `c: L196` of `c: _IO_new_file_overflow`
    (LibioOverflowBase.v describes the function): the buffer is full,
    so the narrow stream flushes all of it, then stores the byte by
    block `c: L198`; a failed flush returns `c: EOF`
    ([wp_ovf_L196]). *)

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
Module LibioOverflowFullOn (R : Runtime) (LG0 : LogicSig R).
Module OB := LibioOverflowBaseOn R LG0.
Import OB OB.SW OB.SW.FI.ML OB.SW.FI.LG OB.SW.FI.L OB.SW.OW OB.SW.FI OB.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The genv defines `c: _IO_new_do_write`. *)
Context (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).

Context (write_ready : Z -> Prop).

Local Instance overflow_full_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

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

(** Block `c: L196`: a full buffer flushed, then the byte ch stored. *)
Lemma wp_ovf_L196 fb freg ch f2 fd eb mode vb vreg bb breg sz we xs fl tw off from e Φ :
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
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L196") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hch Hf2 Hf2r Hfd Happ He Hmd Hv0 Hv2 Hc0 Hc47.
  iIntros "#Hvt Hl Hfx Hst HK". unfold file_size in Hend.
  iDestruct "Hst" as "(%Hp & Hbl & Hxs & Hfl & Htw & Hoff & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend)".
  destruct Hp as (Hbb & Hbe & Hbreg & Hsz & Hkr & Hxl & Hxr & Hwec & Hwea).
  iDestruct "Hfl" as "[%Hflr Hflb]".
  iDestruct "Hfx" as "(Hf2 & Hfd & Herr & Hcol & [%Hm Hmb] & Hvtp)".
  st. st. norm. chk "Hl". load_int "Hl Hmb". st. brm Hmd.
  st. st. norm. chk "Hl".
  iApply (wp_raw_load_pointer with "Hl Hwb Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwb Hbl". st. norm.
  iApply (wp_raw_load_pointer with "Hl Hwp Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwp Hbl".
  iApply (wp_raw_load_pointer with "Hl Hwb Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwb Hbl". st. st. st. norm.
  replace (bb + sz - bb) with sz by lia.
  iApply wp_call_bind; [vx | exact Hdwf | reflexivity |]. iNext.
  iApply (Hovdw with "Hvt Hl [$Hf2 $Hfd $Herr $Hcol $Hmb $Hvtp //] [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend]");
    try first [rewrite Z.mod_small; [reflexivity | lia] | side |
      iApply (ovf_state_intro with "Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); (assumption || lia)].
  iNext. iIntros (r we' fl' tw' off' Hpost) "Hl Hfx Hst".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  assert (Happ' : Z.land fl' io_is_appending = 0)
    by (destruct Hpost as [[_ ->] | [_ ->]]; [exact Happ | rewrite land_lor_const; [exact Happ | reflexivity]]).
  destruct (Z.eq_dec r sz) as [-> | Hrs];
    [rewrite Z.eqb_refl | replace (r =? sz) with false by (symmetry; apply Z.eqb_neq; exact Hrs)].
  - st. st. st. br.
    iApply (HL198 _ _ _ _ _ _ _ _ _ _ _ _ 0 with "Hvt Hl Hfx Hst"); try first [side | lk_prove].
    iNext. iIntros (r k' we'' xs' fl'' tw'' off'' [Hr Hfl'']) "Hl Hfx Hst".
    iApply ("HK" with "[%] Hl Hfx Hst"). split; [exact Hr|].
    destruct Hpost as [[_ ->] | [_ ->]]; destruct Hfl'' as [-> | ->]; unfold io_err_seen;
      rewrite ?lor_err_twice; tauto.
  - st. st. st. br. st. iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hfx Hst").
    split; [right; reflexivity | destruct Hpost as [[_ ->] | [_ ->]]; tauto].
Qed.

End rules.
End LibioOverflowFullOn.
