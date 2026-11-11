(** The end of block `c: iw_1.iw_2.join` of `c: _IO_new_do_write`
    (LibioDoWrite.v describes it), after the jump table's write returned
    r of the n bytes: `c: _cur_column` is 0, so `c: _IO_adjust_column`
    is not called, then the end of the call ([wp_do_write_ret]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: iw_1.iw_2.join` of `c: _IO_new_do_write`; its first 5
    instructions validate and call the jump table's write
    (LibioDoWriteCall.v). *)
Definition dw_join : block := Eval vm_compute in
  match find_block (TAtom "iw_1.iw_2.join") (fn_blocks glibc__IO_new_do_write) with
  | Some b => b | None => mkBlock (TAtom "iw_1.iw_2.join") [] [] JRetVoid end.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioDoWriteRetOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

Local Instance do_write_ret_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The end of the call, as LibioDoWriteTail.v proves it
    ([wp_do_write_tail]). *)
Context (Htail_spec : forall fb freg fl bb breg rp re rb wb wp we be n r e from mode Φ,
  let base := mkPtr bb (Obj bb) in
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= fl < 2 ^ 32 ->
  0 < bb < 2 ^ 63 -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb -> 0 <= r <= n -> n < 2 ^ 63 ->
  (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "iw_1.v67") e = Some (WInt r) ->
  live fb freg -∗ live bb breg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 re -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  ▷ (live fb freg -∗ live bb breg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
     pcell fb off_read_ptr base -∗ pcell fb 16 base -∗ pcell fb 24 base -∗ pcell fb off_write_base base -∗
     pcell fb off_write_ptr base -∗ pcell fb off_write_end (if Z.land fl 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun (mkFrame glibc__IO_new_do_write e [] None (Enter (TAtom "iw_1.L70") (Some from))) : sexpr) {{ Φ }}).


(** The rest of block `c: iw_1.iw_2.join` once the write returned r of
    the n bytes, to the return. *)
Lemma wp_do_write_ret fb freg fl bb breg rp re rb wb wp we be n r e mode Φ :
  let base := mkPtr bb (Obj bb) in
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= fl < 2 ^ 32 ->
  0 < bb < 2 ^ 63 -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb -> 0 <= r <= n -> n < 2 ^ 63 ->
  (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "iw_1.v67") e = Some (WInt r) ->
  live fb freg -∗ live bb breg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 re -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗
  ▷ (live fb freg -∗ live bb breg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
     pcell fb off_read_ptr base -∗ pcell fb 16 base -∗ pcell fb 24 base -∗ pcell fb off_write_base base -∗
     pcell fb off_write_ptr base -∗ pcell fb off_write_end (if Z.land fl 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗ bytes fb off_column [0; 0] -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun (mkFrame glibc__IO_new_do_write e [] None
              (Exec (TAtom "iw_1.iw_2.join") (skipn 5 (b_insts dw_join)) (b_jump dw_join))) : sexpr) {{ Φ }}.
Proof.
  intros base Hfb Hal Hend Hfreg Hfl Hbb Hbe Hbec Hr Hn Hmd Hv0 Hc0 Hv4 Hv67. unfold file_size in Hend.
  iIntros "Hl Hbl Hfl Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol HK".
  cbn [dw_join b_insts b_jump skipn].
  st. norm. chk "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hcol"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | ar |].
  iNext. iIntros "Hl Hcol". br. st. br.
  iApply (Htail_spec with "Hl Hbl Hfl Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend");
    try side.
  iNext. iIntros "Hl Hbl Hfl Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend".
  iApply ("HK" with "Hl Hbl Hfl Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol").
Qed.

End rules.
End LibioDoWriteRetOn.
