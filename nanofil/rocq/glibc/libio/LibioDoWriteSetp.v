(** The second half of block `c: iw_1.L70` of `c: _IO_new_do_write`
    (LibioDoWrite.v describes it), from its fourth store on:
    `c: _IO_setp(fp, base, base)` and the mode's test, then the last
    blocks ([wp_do_write_setp]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioDoWriteCode FileInv LibioLogic SysWrappers.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: iw_1.L70` of `c: _IO_new_do_write`; LibioDoWriteTail.v
    runs its first 16 instructions, `c: _IO_setg(fp, base, base, base)`. *)
Definition dw_L70 : block := Eval vm_compute in
  match find_block (TAtom "iw_1.L70") (fn_blocks glibc__IO_new_do_write) with
  | Some b => b | None => mkBlock (TAtom "iw_1.L70") [] [] JRetVoid end.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioDoWriteSetpOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

Local Instance do_write_setp_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The last blocks, as LibioDoWriteEnd.v proves them
    ([wp_do_write_end]). *)
Context (Hend_spec : forall fb freg fl bb breg we be n r e from Φ,
  let base := mkPtr bb (Obj bb) in
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= fl < 2 ^ 32 ->
  0 < bb < 2 ^ 63 -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb -> 0 <= r <= n -> n < 2 ^ 63 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk16") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  lookup (TAtom "iw_1.v114") e = Some (WPtr (mkPtr (fb + off_write_end) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "iw_1.v67") e = Some (WInt r) ->
  live fb freg -∗ live bb breg -∗ int_cell fb off_flags fl -∗
  pcell fb off_write_end we -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  ▷ (live fb freg -∗ live bb breg -∗ int_cell fb off_flags fl -∗
     pcell fb off_write_end (if Z.land fl 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun (mkFrame glibc__IO_new_do_write e [] None (Enter (TAtom "iw_1.L122") (Some from))) : sexpr) {{ Φ }}).


(** The rest of block `c: iw_1.L70` after `c: _IO_setg`, to the
    return: the write base and pointer the base, and the write end the
    base when `c: _flags` has `c: _IO_LINE_BUF` or `c: _IO_UNBUFFERED`
    (514), the narrow mode being 0 or -1 (`c: _mode <= 0`), else the
    buffer's end. *)
Lemma wp_do_write_setp fb freg fl bb breg wb wp we be n r e mode Φ :
  let base := mkPtr bb (Obj bb) in
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= fl < 2 ^ 32 ->
  0 < bb < 2 ^ 63 -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb -> 0 <= r <= n -> n < 2 ^ 63 ->
  (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk16") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  lookup (TAtom "iw_1.v94") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "iw_1.v67") e = Some (WInt r) ->
  live fb freg -∗ live bb breg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
  pcell fb off_write_base wb -∗ pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  ▷ (live fb freg -∗ live bb breg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
     pcell fb off_write_base base -∗ pcell fb off_write_ptr base -∗
     pcell fb off_write_end (if Z.land fl 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun (mkFrame glibc__IO_new_do_write e [] None
              (Exec (TAtom "iw_1.L70") (skipn 16 (b_insts dw_L70)) (b_jump dw_L70))) : sexpr) {{ Φ }}.
Proof.
  intros base Hfb Hal Hend Hfreg Hfl Hbb Hbe Hbec Hr Hn Hmd Hv0 Hc0 Hc16 Hv94 Hv4 Hv67. unfold file_size in Hend.
  destruct be as [bea bec]. cbn in Hbe, Hbec. subst bec.
  iIntros "Hl Hbl Hfl Hmode Hwb Hwp Hwe Hbase Hbend HK".
  cbn [dw_L70 b_insts b_jump skipn].
  st. st. norm. chk "Hl".
  iApply (wp_raw_load_pointer with "Hl Hbase Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hl Hbase Hbl". chk "Hl".
  iApply (wp_raw_store_pointer with "Hl Hwp"); [vx | vx | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Hl Hwp". chk "Hl".
  iApply (wp_raw_store_pointer with "Hl Hwb"); [vx | vx | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Hl Hwb". st. st. norm. chk "Hl". iDestruct "Hmode" as "[%Hm0 Hmode]". load_int "Hl Hmode".
  st. destruct Hmd as [-> | ->]; br.
  all: iApply (Hend_spec with "Hl Hbl Hfl Hwe Hbase Hbend"); try side;
    iNext; iIntros "Hl Hbl Hfl Hwe Hbase Hbend";
    iApply ("HK" with "Hl Hbl Hfl [$Hmode //] Hwb Hwp Hwe Hbase Hbend").
Qed.


End rules.
End LibioDoWriteSetpOn.
