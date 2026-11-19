From Glibc Require Import Unit_libio_fileops_os.
From Glibc Require Import GlibcProgram.
(** After a write, glibc resets the stream's write end according to its buffering mode.
    A line-buffered or unbuffered stream uses the buffer's base; other streams use its end.
    The function returns zero after a complete write and EOF after a short write. *)

From Glibc Require Import GlibcTactics LibioTactics GlibcSymFunc.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers.
From Glibc Require FileInv LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A stream in narrow mode resets its write end and reports whether the write was complete. *)
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
  WP (ERun (mkFrame Unit_libio_fileops_os.fn__IO_new_do_write e [] None (Enter (TAtom "iw_1.L122") (Some from))) : sexpr) {{ Φ }}.
Proof using Type.
  intros base Hfb Hal Hend Hfreg Hfl Hbb Hbe Hbec Hr Hn Hv0 Hc0 Hc16 Hv114 Hv4 Hv67. unfold file_size in Hend.
  destruct be as [bea bec]. cbn in Hbe, Hbec. subst bec.
  iIntros "Hl Hbl Hfl Hwe Hbase Hbend HK".
  step. iDestruct "Hfl" as "[%Hfl0 Hfl]". unfold int_bytes, base.
  sym_frun_with "Hl Hbl Hfl Hwe Hbase Hbend" (@nil name)
    ltac:(first [GlibcSym.sym_lia | eexists; split; [reflexivity|]; unfold GlibcSym.cell_pieces; wi_store]) ltac:(sym_vm).
  all: cbn [cond_bit GlibcSym.bitden] in *.
  all: destruct (Z.land fl 514 =? 0) eqn:E514; destruct (r =? n) eqn:Ern; cbn in *;
    try (exfalso; GlibcSym.sym_lia).
  all: iApply wp_ret; [reflexivity | vx |]; iNext.
  all: rewrite Z.mod_small; [|lia].
  all: iApply ("HK" with "Hl Hbl [$Hfl //] Hwe Hbase Hbend").
Qed.

End rules.
