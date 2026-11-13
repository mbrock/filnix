(** This file proves block `c: L198` of `c: _IO_new_file_overflow`
    (LibioOverflowBase.v describes the function): the byte goes to
    `c: _IO_write_ptr`, which advances, and an unbuffered stream, or a
    line-buffered one given a newline, is flushed by block `c: L264`
    ([wp_ovf_L198]). *)

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
Module LibioOverflowPutOn (R : Runtime) (LG0 : LogicSig R).
Module OB := LibioOverflowBaseOn R LG0.
Import OB OB.SW OB.SW.FI.ML OB.SW.FI.LG OB.SW.FI.L OB.SW.OW OB.SW.FI OB.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

Context (write_ready : Z -> Prop).

Local Instance overflow_put_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L264`, as LibioOverflowFlush.v proves it ([wp_ovf_L264]). *)
Context (HL264 : forall fb freg ch f2 fd eb mode vb vreg bb breg sz k we xs fl tw off from e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= ch < 256 -> 0 < k ->
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
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L264") (Some from))) : sexpr) {{ Φ }}).

(** Block `c: L198`: the byte ch stored at the write pointer of a
    buffer with room, then the flush when one is due. *)
Lemma wp_ovf_L198 fb freg ch f2 fd eb mode vb vreg bb breg sz k we xs fl tw off from e Φ :
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
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L198") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hch Hk Hf2 Hf2r Hfd Happ He Hmd Hv0 Hv2 Hc0 Hc47.
  iIntros "#Hvt Hl Hfx Hst HK". unfold file_size in Hend.
  iDestruct "Hst" as "(%Hp & Hbl & Hxs & Hfl & Htw & Hoff & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend)".
  destruct Hp as (Hbb & Hbe & Hbreg & Hsz & Hkr & Hxl & Hxr & Hwec & Hwea).
  st. st. norm. chk "Hl".
  iApply (wp_raw_load_pointer with "Hl Hwp Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwp Hbl". st. norm. chk "Hl".
  iApply (wp_raw_store_pointer with "Hl Hwp"); [vx | vx | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Hl Hwp". st. norm. chk "Hbl".
  iDestruct (bytes_focus bb xs (Z.to_nat k) with "Hxs") as "(Hx0 & Hx1 & Hx2)"; [lia|].
  rewrite Z2Nat.id; [|lia].
  iApply (wp_raw_store_byte with "Hbl Hx1"); [vx | vx | reflexivity | ar | wi_store |].
  iNext. iIntros "Hbl Hx1". rewrite (sb_byte ch Hch) -Z.add_assoc.
  iPoseProof (bytes_unfocus bb xs (Z.to_nat k) ch with "Hx0") as "U"; [lia|]. rewrite Z2Nat.id; [|lia].
  iDestruct ("U" with "Hx1 Hx2") as "Hxs".
  iDestruct "Hfl" as "[%Hflr Hflb]". chk "Hl". load_int "Hl Hflb". st.
  assert (H2 : 0 <= Z.land fl 2 < 2 ^ 32) by (apply land_lt32; lia).
  assert (H512 : 0 <= Z.land fl 512 < 2 ^ 32) by (apply land_lt32; lia).
  assert (Hxs' : length (<[Z.to_nat k := ch]> xs) = Z.to_nat sz /\ Forall (fun x => 0 <= x < 256) (<[Z.to_nat k := ch]> xs))
    by (rewrite length_insert; split; [exact Hxl | apply Forall_insert; [exact Hxr | lia]]).
  destruct Hxs' as [Hxl' Hxr'].
  destruct (Z.eq_dec (Z.land fl 2) 0) as [Hu | Hu].
  - brv true. st. load_int "Hl Hflb". st.
    destruct (Z.eq_dec (Z.land fl 512) 0) as [Hlb | Hlb].
    + brv true. st. br. st. st. iApply wp_ret; [reflexivity | vx |]. iNext. rewrite (ret_byte ch Hch).
      iApply ("HK" with "[%] Hl Hfx [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend]");
        [split; left; reflexivity | iApply (ovf_state_intro with "Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); (assumption || lia)].
    + brv false. st. st. st. st. destruct (Z.eq_dec ch 10) as [-> | Hc10].
      * brv false.
        iApply (HL264 _ _ _ _ _ _ _ _ _ _ _ _ (k + 1) with "Hvt Hl Hfx [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend] HK");
          try first [side | lia | iApply (ovf_state_intro with "Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); (assumption || lia)].
      * brv true. st. st. iApply wp_ret; [reflexivity | vx |]. iNext. rewrite (ret_byte ch Hch).
        iApply ("HK" with "[%] Hl Hfx [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend]");
          [split; left; reflexivity | iApply (ovf_state_intro with "Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); (assumption || lia)].
  - brv false. st. br.
    iApply (HL264 _ _ _ _ _ _ _ _ _ _ _ _ (k + 1) with "Hvt Hl Hfx [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend] HK");
      try first [side | lia | iApply (ovf_state_intro with "Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); (assumption || lia)].
Qed.

End rules.
End LibioOverflowPutOn.
