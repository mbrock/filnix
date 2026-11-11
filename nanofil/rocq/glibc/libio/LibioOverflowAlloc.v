(** The first overflow of a stream allocates its buffer, switches it to
    writing, and sends the requested byte. This file proves the whole
    function from the proof of its allocation block. The result retains
    the fresh buffer's alignment, heap ownership and empty capability
    slots, which later copies and stream closure need. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv LibioLogic
  SysWrappers LibioSetb LibioOverflowBase LibioOverflowAllocSetg.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioOverflowAllocOn (R : Runtime) (LG0 : LogicSig R).
Module OB := LibioOverflowBaseOn R LG0.
Import OB OB.SW OB.SW.FI.ML OB.SW.FI.LG OB.SW.FI.L OB.SW.OW OB.SW.FI OB.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

Local Instance overflow_alloc_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The allocator's state, which `c: malloc` takes and gives back. *)
Context (Mres : iProp Σ).
(** Block `c: L33`, as LibioOverflowAllocSetg.v proves it ([wp_ovf_L33]). *)
Context (HL33 : forall fb freg ch f2 fd eb mode vb vreg fl tw off rp re rb wp0 we0 oe from e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  Z.land fl io_is_appending = 0 -> Z.land fl 8 = 0 -> Z.land fl 2048 = 0 -> Z.land fl 256 = 0 ->
  Z.land fl io_unbuffered = 0 -> ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk6") e = Some (WPtr (mkPtr (fb + off_write_base) (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  int_cell fb off_flags fl -∗ icell fb off_total_written tw -∗ icell fb off_offset off -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 re -∗ pcell fb 24 rb -∗ pcell fb off_write_base null -∗
  pcell fb off_write_ptr wp0 -∗ pcell fb off_write_end we0 -∗ pcell fb off_buf_base null -∗
  pcell fb off_buf_end oe -∗ Mres -∗
  ▷ (∀ r bb breg sz k' we' xs' fl' tw' off',
     ⌜ovf_ret ch r /\ 0 < sz <= 8192 /\ ovf_alloc_flags fl fl' /\
       r_kind breg = Heap /\ bb mod 16 = 0 /\ r_end breg <= 2 ^ 48⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     auxes bb 0 (replicate (Z.to_nat sz) CNone) -∗ Mres -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L33") (Some from))) : sexpr) {{ Φ }}).

(** `c: _IO_new_file_overflow(fp, ch)` on a stream with no buffer that
    is not putting: the stream gets a buffer of 1 to 8192 bytes, puts
    into it, and takes ch. *)
Lemma wp_glibc__IO_new_file_overflow_alloc fr fb freg ch f2 fd eb mode vb vreg fl tw off rp re rb wp0 we0 oe Φ :
  call_frame glibc__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  Z.land fl io_is_appending = 0 -> Z.land fl 8 = 0 -> Z.land fl 2048 = 0 -> Z.land fl 256 = 0 ->
  Z.land fl io_unbuffered = 0 -> ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  int_cell fb off_flags fl -∗ icell fb off_total_written tw -∗ icell fb off_offset off -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 re -∗ pcell fb 24 rb -∗ pcell fb off_write_base null -∗
  pcell fb off_write_ptr wp0 -∗ pcell fb off_write_end we0 -∗ pcell fb off_buf_base null -∗
  pcell fb off_buf_end oe -∗ Mres -∗
  ▷ (∀ r bb breg sz k' we' xs' fl' tw' off',
     ⌜ovf_ret ch r /\ 0 < sz <= 8192 /\ ovf_alloc_flags fl fl' /\
       r_kind breg = Heap /\ bb mod 16 = 0 /\ r_end breg <= 2 ^ 48⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     auxes bb 0 (replicate (Z.to_nat sz) CNone) -∗ Mres -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hfreg Hch Hf2 Hf2r Hfd Hfd31 Happ Hnw Hnp Hbk Hub He Hmd. injection Hfr as <-.
  iIntros "#Hvt Hl Hfx [%Hflr Hflb] Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend HM HK". unfold file_size in Hend.
  iDestruct "Hfx" as "(Hf2 & Hfd & Herr & Hcol & Hmode & Hvtp)".
  assert (H2048 : 0 <= Z.land fl 2048 < 2 ^ 32) by (apply land_lt32; lia).
  enter. adv. load_int "Hl Hflb". adv. brv true.
  adv. load_int "Hl Hflb". adv. brv false.
  adv. br. adv.
  iApply (wp_raw_load_pointer with "Hl Hwb [//]"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwb _". adv. br.
  iApply (HL33 with "Hvt Hl [$Hf2 $Hfd $Herr $Hcol $Hmode $Hvtp] [$Hflb //] Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend HM HK");
    try first [side | lk_prove].
  Unshelve. all: exact freg.
Qed.

End rules.
End LibioOverflowAllocOn.
