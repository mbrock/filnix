(** The last blocks of `c: _IO_new_do_write` (LibioDoWrite.v
    describes it), from `c: iw_1.L122`: the write end is the buffer's
    base when the stream is line-buffered or unbuffered, else its end,
    and the result is 0 when the write took all n bytes, else
    `c: EOF` ([wp_do_write_end]). *)

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

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioDoWriteEndOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

Local Instance do_write_end_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: iw_1.L122` of `c: _IO_new_do_write` to its return, the
    mode being 0 and r of the n bytes written. *)
Lemma wp_do_write_end fb freg fl bb breg we be n r e from Φ :
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
  WP (ERun (mkFrame glibc__IO_new_do_write e [] None (Enter (TAtom "iw_1.L122") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros base Hfb Hal Hend Hfreg Hfl Hbb Hbe Hbec Hr Hn Hv0 Hc0 Hc16 Hv114 Hv4 Hv67. unfold file_size in Hend.
  destruct be as [bea bec]. cbn in Hbe, Hbec. subst bec.
  iIntros "Hl Hbl Hfl Hwe Hbase Hbend HK".
  st. chk "Hl". iDestruct "Hfl" as "[%Hfl0 Hfl]". load_int "Hl Hfl". st. st. st.
  assert (Hm514 : 0 <= Z.land fl 514 < 2 ^ 32) by (apply land_lt32; lia).
  destruct (Z.land fl 514 =? 0) eqn:E514; [apply Z.eqb_eq in E514 | apply Z.eqb_neq in E514].
  - st. brv true. st. st. norm. chk "Hl".
    iApply (wp_raw_load_pointer with "Hl Hbend Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
    iNext. iIntros "Hl Hbend Hbl". st. st. chk "Hl".
    iApply (wp_raw_store_pointer with "Hl Hwe"); [vx | vx | reflexivity | ar | ar | wi_store |].
    iNext. iIntros "Hl Hwe". st. st. st. st. st.
    destruct (Z.eq_dec r n) as [-> | Hrn].
    + brv false. st. iApply wp_ret; [reflexivity | vx |]. iNext. rewrite Z.eqb_refl.
      iApply ("HK" with "Hl Hbl [$Hfl //] [Hwe] Hbase Hbend"). replace (Z.land fl 514 =? 0) with true by (symmetry; apply Z.eqb_eq; exact E514). iExact "Hwe".
    + brv true. st. st. st. iApply wp_ret; [reflexivity | vx |]. iNext.
      replace (r =? n) with false by (symmetry; apply Z.eqb_neq; exact Hrn).
      iApply ("HK" with "Hl Hbl [$Hfl //] [Hwe] Hbase Hbend"). replace (Z.land fl 514 =? 0) with true by (symmetry; apply Z.eqb_eq; exact E514). iExact "Hwe".
  - st. brv false. st. st. norm. chk "Hl".
    iApply (wp_raw_load_pointer with "Hl Hbase Hbl"); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |].
    iNext. iIntros "Hl Hbase Hbl". st. st. chk "Hl".
    iApply (wp_raw_store_pointer with "Hl Hwe"); [vx | vx | reflexivity | ar | ar | wi_store |].
    iNext. iIntros "Hl Hwe". st. st. st. st. st.
    destruct (Z.eq_dec r n) as [-> | Hrn].
    + brv false. st. iApply wp_ret; [reflexivity | vx |]. iNext. rewrite Z.eqb_refl.
      iApply ("HK" with "Hl Hbl [$Hfl //] [Hwe] Hbase Hbend"). replace (Z.land fl 514 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E514). iExact "Hwe".
    + brv true. st. st. st. iApply wp_ret; [reflexivity | vx |]. iNext.
      replace (r =? n) with false by (symmetry; apply Z.eqb_neq; exact Hrn).
      iApply ("HK" with "Hl Hbl [$Hfl //] [Hwe] Hbase Hbend"). replace (Z.land fl 514 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E514). iExact "Hwe".
Qed.

End rules.
End LibioDoWriteEndOn.
