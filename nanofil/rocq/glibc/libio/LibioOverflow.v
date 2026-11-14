(** This file proves the triple of `c: _IO_new_file_overflow` (LibioOverflowBase.v
    describes the function) on a stream that is already putting into
    its buffer, as it is after the first call
    ([wp_glibc__IO_new_file_overflow]). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv LibioLogic
  SysWrappers LibioOverflowBase.
From Glibc Require FileInv LibioLogic LibioOverflowBase OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioOverflowBase SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

Context (write_ready : Z -> Prop).

Local Instance overflow_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L18`, as LibioOverflowSend.v proves it ([wp_ovf_L18]). *)
Context (HL18 : forall fb freg ch f2 fd eb mode vb vreg bb breg sz k we xs fl tw off from e Φ,
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
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L18") (Some from))) : sexpr) {{ Φ }}).

(** `c: _IO_new_file_overflow(fp, ch)` on a stream putting into its
    buffer: ch is stored after a flush of a full buffer, or `c: EOF`
    flushes the buffer. *)
Lemma wp_glibc__IO_new_file_overflow fr fb freg ch f2 fd eb mode vb vreg bb breg sz k we xs fl tw off Φ :
  call_frame glibc__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  write_ready f2 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  Z.land fl 8 = 0 -> Z.land fl 2048 <> 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  ovf_state fb bb breg sz k we xs fl tw off -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜ovf_ret ch r /\ (fl' = fl \/ fl' = Z.lor fl io_err_seen)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hfreg Hch Hf2 Hf2r Hfd Happ Hnw Hput He Hmd. injection Hfr as <-.
  iIntros "#Hvt Hl Hfx Hst HK". unfold file_size in Hend.
  iDestruct "Hst" as "(%Hp & Hbl & Hxs & [%Hflr Hflb] & Htw & Hoff & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend)".
  destruct Hp as (Hbb & Hbe & Hbreg & Hsz & Hkr & Hxl & Hxr & Hwec & Hwea).
  step. adv. load_s32_group "Hl Hflb". adv. branch_as true.
  assert (H2048 : 0 <= Z.land fl 2048 < 2 ^ 32) by (apply land_lt32; lia).
  adv. load_s32_group "Hl Hflb". adv. branch_as true.
  adv. iApply (wp_raw_load_pointer with "Hl Hwb Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwb Hbl". step. step. step. step. step. branch_as true.
  iApply (HL18 with "Hvt Hl Hfx [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend] HK");
    try first [libio_side | lk_prove |
      iApply (ovf_state_intro with "Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); (assumption || lia)].
Qed.

End rules.
