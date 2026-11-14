From Glibc Require Import GlibcProgram.
(** After a write, the stream resets its write pointers and tests its mode.
    One symbolic run covers the pointer stores and the mode test.
    The continuation chooses the write end and returns the result. *)

From Glibc Require Import GlibcTactics LibioTactics GlibcSymFunc.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioDoWriteCode FileInv LibioLogic SysWrappers.
From Glibc Require FileInv LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The reset block first restores the read pointers, then resets the write pointers.
    LibioDoWriteTail.v proves the first sixteen instructions of this block. *)
Definition dw_L70 : block := Eval vm_compute in
  match find_block (TAtom "iw_1.L70") (fn_blocks glibc__IO_new_do_write) with
  | Some b => b | None => mkBlock (TAtom "iw_1.L70") [] [] JRetVoid end.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The continuation chooses the write end from the stream flags and returns the write result.
    LibioDoWriteEnd.v proves this contract. *)
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


(** Both write pointers return to the buffer's base after the read pointers have been reset.
    Line-buffered and unbuffered streams also set the write end to that base.
    Other streams retain the buffer's end as their write end. *)
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
  iDestruct "Hmode" as "[%Hm0 Hmode]". unfold int_bytes, base.
  sym_frun_with "Hl Hbl Hbase Hwp Hwb Hmode" [TAtom "iw_1.L122"]
    ltac:(first [GlibcSym.sym_lia | eexists; split; [reflexivity|]; unfold GlibcSym.cell_pieces; wi_store]) ltac:(sym_vm).
  all: destruct Hmd as [-> | ->].
  all: try (exfalso; vm_compute in Hsym_yes; contradiction).
  all: try (exfalso; vm_compute in Hsym_no; discriminate).
  all: iApply (Hend_spec with "Hl Hbl Hfl Hwe Hbase Hbend"); try libio_side;
    iNext; iIntros "Hl Hbl Hfl Hwe Hbase Hbend";
    iApply ("HK" with "Hl Hbl Hfl [$Hmode //] Hwb Hwp Hwe Hbase Hbend").
Qed.


End rules.
