From Glibc Require Import GlibcProgram.
(** The end of `c: _IO_new_do_write` (LibioDoWrite.v describes it),
    after the jump table's write returned r of the n bytes: every read
    and write pointer is the buffer's base, the write end the base or
    the buffer's end, and the result is 0 when r is n, else
    `c: EOF` ([wp_do_write_tail]). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioDoWriteCode FileInv LibioLogic SysWrappers LibioDoWriteSetp.
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

(** The rest of block `c: iw_1.L70`, as LibioDoWriteSetp.v proves it
    ([wp_do_write_setp]). *)
Context (Hsetp_spec : forall fb freg fl bb breg wb wp we be n r e mode Φ,
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
              (Exec (TAtom "iw_1.L70") (skipn 16 (b_insts dw_L70)) (b_jump dw_L70))) : sexpr) {{ Φ }}).

(** Each rule application repeats the whole current frame, so a long proof
    walks the same environment and instruction list once per step. These
    tactics keep both behind local definitions: the environment is named
    after every step, the remaining instructions are a chain of definitions
    whose bodies hold one instruction each, and only the next instruction is
    shown. The block's final jump stays named until no instruction is left. The rules see the same frame up to unfolding those definitions. *)
Local Ltac chain_tail L :=
  lazymatch L with
  | _ :: ?R => first [lazymatch R with _ :: _ => chain_tail R end | let X := fresh "I" in set (X := L)]
  end.
Local Ltac tidy :=
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ ?L _))) _) => is_var L; unfold L
  end;
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ [] ?J))) _) => is_var J; unfold J
  end;
  repeat lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ (_ :: ?R) _))) _) =>
      lazymatch R with _ :: _ => chain_tail R end
  end;
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ (_ :: _) ?J))) _) =>
      first [is_var J | let X := fresh "J" in set (X := J)]
  end;
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ ?e _ _ _)) _) =>
      lazymatch e with put _ _ _ => let E := fresh "Env" in set (E := e) end
  end.
(** When a function calls another one, the proof uses the callee's
    specification, and every premise it gives up repeats what happens after
    the call. This tactic names that remainder and the callee's starting
    state first, and the caller unfolds the remainder when the call returns. *)
Local Ltac name_post :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ ?F) ?Q) =>
      let X := fresh "Post" in set (X := Q); let Y := fresh "Callee" in set (Y := F)
  end.
(** Block `c: iw_1.L70` of `c: _IO_new_do_write` to its return, r of
    the n bytes written: `c: _IO_setg(fp, base, base, base)`, the
    write base and pointer the base too, and the write end the base
    when `c: _flags` has `c: _IO_LINE_BUF` or `c: _IO_UNBUFFERED`
    (514), the narrow mode being 0 or -1, else the buffer's end. *)
Lemma wp_do_write_tail fb freg fl bb breg rp re rb wb wp we be n r e from mode Φ :
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
  WP (ERun (mkFrame glibc__IO_new_do_write e [] None (Enter (TAtom "iw_1.L70") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros base Hfb Hal Hend Hfreg Hfl Hbb Hbe Hbec Hr Hn Hmd Hv0 Hc0 Hv4 Hv67. unfold file_size in Hend.
  destruct be as [bea bec]. cbn in Hbe, Hbec. subst bec.
  iIntros "Hl Hbl Hfl Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend HK".
  tidy. step_entailment ltac:(idtac); tidy. step; tidy. step. norm; tidy. check "Hl"; tidy.
  load_pointer "Hl Hbase Hbl" by ar.
  iNext. iIntros "Hl Hbase Hbl". tidy. check "Hl"; tidy.
  store_pointer "Hl Hrb" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hrb". tidy. step. norm; tidy. check "Hl"; tidy.
  load_pointer "Hl Hbase Hbl" by ar.
  iNext. iIntros "Hl Hbase Hbl". tidy. check "Hl"; tidy.
  store_pointer "Hl Hrp" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hrp". tidy. step. norm; tidy. check "Hl"; tidy.
  load_pointer "Hl Hbase Hbl" by ar.
  iNext. iIntros "Hl Hbase Hbl". tidy. check "Hl"; tidy.
  store_pointer "Hl Hre" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hre". tidy.
  iApply (Hsetp_spec with "Hl Hbl Hfl Hmode Hwb Hwp Hwe Hbase Hbend"); try libio_side.
  iNext. iIntros "Hl Hbl Hfl Hmode Hwb Hwp Hwe Hbase Hbend".
  iApply ("HK" with "Hl Hbl Hfl Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend").
Qed.


End rules.
