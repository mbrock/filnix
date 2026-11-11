(** This file proves block `c: L264` of `c: _IO_new_file_overflow`
    (LibioOverflowBase.v describes the function): the flush after the
    byte was stored, which returns the byte, or `c: EOF` when the write
    failed ([wp_ovf_L264]). *)

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
Module LibioOverflowFlushOn (R : Runtime) (LG0 : LogicSig R).
Module OB := LibioOverflowBaseOn R LG0.
Import OB OB.SW OB.SW.FI.ML OB.SW.FI.LG OB.SW.FI.L OB.SW.OW OB.SW.FI OB.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The genv defines `c: _IO_new_do_write`. *)
Context (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).

Local Instance overflow_flush_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_new_do_write` from the buffer's base, as LibioDoWrite.v's
    [wp_glibc__IO_new_do_write_base] proves it. *)
Context (Hdw : forall fr fb freg fl f2 fd tw off bb breg xs rp rb wp we be eb vb vreg mode Φ,
  let n := Z.of_nat (length xs) in
  let base := mkPtr bb (Obj bb) in
  call_frame glibc__IO_new_do_write [WPtr (mkPtr fb (Obj fb)); WPtr base; WInt n] = Some fr -> 0 < n ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < bb -> bb + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb ->
  (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb 0 xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 base -∗ pcell fb 24 rb -∗ pcell fb off_write_base base -∗
  pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode mode -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post n fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live bb breg -∗ bytes bb 0 xs -∗ errno_any eb -∗
     pcell fb off_read_ptr base -∗ pcell fb 16 base -∗ pcell fb 24 base -∗ pcell fb off_write_base base -∗
     pcell fb off_write_ptr base -∗ pcell fb off_write_end (if Z.land fl' 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode mode -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}).

(** Block `c: L264`: the flush of the k pending bytes, returning the
    byte ch or `c: EOF`. *)
Lemma wp_ovf_L264 fb freg ch f2 fd eb mode vb vreg bb breg sz k we xs fl tw off from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= ch < 256 -> 0 < k ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk47") e = Some (WPtr (mkPtr (fb + off_write_ptr) (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  ovf_state fb bb breg sz k we xs fl tw off -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜(r = ch \/ r = 2 ^ 32 - 1) /\ (fl' = fl \/ fl' = Z.lor fl io_err_seen)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L264") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hch Hk Hf2 Hf2r Hfd Happ He Hmd Hv0 Hv2 Hc0 Hc47.
  iIntros "#Hvt Hl Hfx Hst HK". unfold file_size in Hend.
  iDestruct "Hst" as "(%Hp & Hbl & Hxs & Hfl & Htw & Hoff & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend)".
  destruct Hp as (Hbb & Hbe & Hbreg & Hsz & Hkr & Hxl & Hxr & Hwec & Hwea).
  st. st. norm. chk "Hl".
  iApply (wp_raw_load_pointer with "Hl Hwb Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwb Hbl". st. norm. chk "Hl".
  iApply (wp_raw_load_pointer with "Hl Hwp Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwp Hbl".
  iApply (wp_raw_load_pointer with "Hl Hwb Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hwb Hbl". st. st. st. norm.
  iDestruct (bytes_take_drop bb 0 xs (Z.to_nat k) with "Hxs") as "[Hxs Hxs2]"; [lia|].
  replace (bb + k - bb) with (Z.of_nat (length (take (Z.to_nat k) xs))) by (rewrite length_take; lia).
  iDestruct "Hfx" as "(Hf2 & Hfd & Herr & Hcol & Hmode & Hvtp)".
  iApply wp_call_bind; [vx | exact Hdwf | reflexivity |]. iNext.
  iDestruct "Hfl" as "[%Hflr Hflb]".
  iApply (Hdw with "Hvt Hl [$Hflb //] Hf2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp");
    try first [rewrite Z.mod_small; [reflexivity | rewrite length_take; lia] | side | rewrite length_take; lia |
               apply Forall_take; exact Hxr].
  iNext. iIntros (r fl' tw' off' [Hpost Hfl']) "Hl Hfl Hf2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iCombine "Hxs Hxs2" as "Hxs". rewrite -bytes_take_drop; [|lia].
  assert (Hwe' : ptr_cap (if Z.land fl' 514 =? 0 then mkPtr (bb + sz) (Obj bb) else mkPtr bb (Obj bb)) = Obj bb /\
                 bb <= ptr_addr (if Z.land fl' 514 =? 0 then mkPtr (bb + sz) (Obj bb) else mkPtr bb (Obj bb)) <= bb + sz)
    by (destruct (Z.land fl' 514 =? 0); cbn; (split; [reflexivity | lia])).
  iDestruct (ovf_state_base with "Hbl Hxs [$Hfl //] Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend") as "Hst";
    try first [lia | tauto].
  iCombine "Hf2 Hfd Herr Hcol Hmode Hvtp" as "Hfx".
  st. destruct Hpost as [[-> ->] | [Hr ->]].
  - rewrite Z.eqb_refl. br. st. st. iApply wp_ret; [reflexivity | vx |]. iNext.
    rewrite (ret_byte ch Hch). iApply ("HK" with "[%] Hl Hfx Hst"). split; left; reflexivity.
  - replace (r =? _) with false by (symmetry; apply Z.eqb_neq; lia). br. st.
    iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hfx Hst"). split; right; reflexivity.
Qed.

End rules.
End LibioOverflowFlushOn.
