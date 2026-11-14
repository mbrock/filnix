(** This file proves block `c: L113` of `c: _IO_new_file_overflow`
    (LibioOverflowBase.v describes the function), the switch to
    putting: the write pointers start at the read pointer and end at
    the buffer's end ([wp_ovf_L113]). LibioOverflowSetpRest.v proves
    the rest of the block. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv LibioLogic
  SysWrappers LibioOverflowBase LibioOverflowSetpRest.
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

Local Instance overflow_setp_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The rest of block `c: L113`, as LibioOverflowSetpRest.v proves it
    ([wp_ovf_L113_rest]). *)
Context (HL113r : forall fb freg ch f2 fd eb mode vb vreg bb breg sz xs fl tw off rest j e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  rest = skipn 17 (b_insts ovf_b113) -> j = b_jump ovf_b113 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk24") e = Some (WPtr (mkPtr (fb + off_read_ptr) (Obj fb))) ->
  lookup (TAtom "v133") e = Some (WPtr (mkPtr (fb + off_read_ptr) (Obj fb))) ->
  lookup (TAtom "chk30") e = Some (WPtr (mkPtr (fb + off_write_ptr) (Obj fb))) ->
  lookup (TAtom "chk34") e = Some (WPtr (mkPtr (fb + off_write_end) (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  ovf_state fb bb breg sz 0 (mkPtr (bb + sz) (Obj bb)) xs fl tw off -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜ovf_ret ch r /\ (fl' = Z.lor fl 2048 \/ fl' = Z.lor (Z.lor fl 2048) io_err_seen)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Exec (TAtom "L113") rest j)) : sexpr) {{ Φ }}).

(** Block `c: L113`: the switch to putting on a buffer whose read
    pointers are at its base. *)
Lemma wp_ovf_L113 fb freg ch f2 fd eb mode vb vreg bb breg sz xs fl tw off wb0 wp0 we0 from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  Z.land fl 256 = 0 -> ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  0 < bb -> bb + sz <= r_end breg -> r_end breg <= 2 ^ 63 -> 0 < sz -> length xs = Z.to_nat sz ->
  Forall (fun x => 0 <= x < 256) xs ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk6") e = Some (WPtr (mkPtr (fb + off_write_base) (Obj fb))) ->
  lookup (TAtom "chk24") e = Some (WPtr (mkPtr (fb + off_read_ptr) (Obj fb))) ->
  lookup (TAtom "chk25") e = Some (WPtr (mkPtr (fb + off_buf_end) (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  live bb breg -∗ bytes bb 0 xs -∗ int_cell fb off_flags fl -∗ icell fb off_total_written tw -∗
  icell fb off_offset off -∗ pcell fb off_read_ptr (mkPtr bb (Obj bb)) -∗ pcell fb 16 (mkPtr bb (Obj bb)) -∗
  pcell fb 24 (mkPtr bb (Obj bb)) -∗ pcell fb off_write_base wb0 -∗ pcell fb off_write_ptr wp0 -∗
  pcell fb off_write_end we0 -∗ pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗
  pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜ovf_ret ch r /\ (fl' = Z.lor fl 2048 \/ fl' = Z.lor (Z.lor fl 2048) io_err_seen)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L113") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hch Hf2 Hf2r Hfd Happ Hbk He Hmd Hbb Hbe Hbreg Hsz Hxl Hxr Hv0 Hv2 Hc0 Hc6 Hc24 Hc25.
  iIntros "#Hvt Hl Hfx Hbl Hxs [%Hflr Hflb] Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend HK".
  unfold file_size in Hend.
  adv. iApply (wp_raw_load_pointer with "Hl Hrp Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hrp Hbl". adv.
  iApply (wp_raw_store_pointer with "Hl Hwp"); [vx | vx | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Hl Hwp". adv.
  iApply (wp_raw_load_pointer with "Hl Hwp Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwp Hbl". adv.
  iApply (wp_raw_store_pointer with "Hl Hwb"); [vx | vx | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Hl Hwb". adv.
  iApply (wp_raw_load_pointer with "Hl Hbend Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hbend Hbl". adv.
  iApply (wp_raw_store_pointer with "Hl Hwe"); [vx | vx | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Hl Hwe".
  iApply (HL113r with "Hvt Hl Hfx [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend] HK");
    try first [reflexivity | libio_side | lk_prove |
      iApply (ovf_state_base with "Hbl Hxs [$Hflb //] Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend");
        try first [assumption | reflexivity | cbn; lia]].
Qed.

End rules.
