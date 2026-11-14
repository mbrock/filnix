(** The middle of one pass of `c: _IO_unbuffer_all`'s loop in
    `c: _IO_cleanup` (LibioCleanupCode.v), from block `c: iw_1.L93`,
    with the stream locked. The pass frees a backup area if the
    stream has one, frees the wide backup area of a wide stream, and
    gives up the buffer of a buffered stream whose mode is set, with
    `c: _IO_SETBUF (fp, NULL, 0)`. Last it sets the mode to -1.

    Here `c: _IO_backup_base` is null and the stream narrow, so the
    first two do nothing. Either `c: _IO_UNBUFFERED` is set, as for
    `c: stderr`, or the mode is still 0, as for an unused `c: stdin`,
    so `c: _IO_SETBUF` is not called. The pass stores -1 in
    `c: _mode` and, since `c: _IO_USER_LOCK` is clear, goes on to
    release the lock at `c: iw_1.L306` (LibioCleanupFpUnlock.v). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry LibioCleanupCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean LibioFlushStart
  LibioFlushTail LibioFlushBody LibioFlush LibioCleanupFpLock.
From Glibc Require FileInv LibioCleanupFpLock LibioCloseSteps LibioFlush LibioFlushBody LibioFlushClean LibioFlushFpLock LibioFlushFpUnlock LibioFlushStart LibioFlushTail LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioCleanupFpLock LibioFlush LibioFlushBody LibioFlushTail LibioFlushStart LibioFlushClean LibioFlushFpUnlock LibioFlushFpLock LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance cleanup_mode_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A branch on a mode test, decided by the equation E. *)


(** Block `c: iw_1.L93` of `c: _IO_cleanup` to block `c: iw_1.L306`,
    the locked stream fb in `c: iw_1.pr.1` and `c: chk13`: with no
    backup area, a narrow mode md, and `c: _IO_UNBUFFERED` set or md
    0, nothing is called and the mode becomes -1. *)
Lemma wp_cleanup_L93 e fb freg fl md r cb Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "iw_1.pr.1") e = Some (WPtr fp) -> lookup (TAtom "chk13") e = Some (WPtr fp) ->
  lookup (TAtom "v1") e = Some (WInt r) -> lookup (TAtom "iw_1.v2") e = Some (WPtr cb) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> md = 0 \/ md = 2 ^ 32 - 1 -> Z.land fl io_unbuffered <> 0 \/ md = 0 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode md -∗ pcell fb 80 null -∗
  ▷ (∀ e', ⌜lookup (TAtom "iw_1.pr.1") e' = Some (WPtr fp) /\ lookup (TAtom "chk13") e' = Some (WPtr fp) /\
            lookup (TAtom "v1") e' = Some (WInt r) /\ lookup (TAtom "iw_1.v2") e' = Some (WPtr cb)⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode (2 ^ 32 - 1) -∗ pcell fb 80 null -∗
     WP (ERun (mkFrame glibc__IO_cleanup e' [] None (Enter (TAtom "iw_1.L306") (Some (TAtom "iw_1.L291"))))
          : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_cleanup e [] None (Enter (TAtom "iw_1.L93") (Some (TAtom "iw_1.L103"))))
       : sexpr) {{ Φ }}.
Proof.
  intros fp Hp1 Hc13 Hv1 Hv2 Hfb Hfal Hfend Hfreg Hul Hmd Hub. subst fp.
  unfold file_size in Hfend. unfold io_unbuffered in Hub.
  iIntros "Hl [%Hflr Hfl] [%Hmdr Hmd] H80 HK".
  assert (0 <= Z.land fl 32768 < 2 ^ 32) by (rewrite Hul; lia).
  assert (0 <= Z.land fl 2 < 2 ^ 32) by (apply land_lt32; lia).
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  (* iw_1.L93, iw_1.L194, iw_1.L203: no backup area, and narrow. *)
  step. step. check "Hl". load_null "Hl" "H80". step. step. step. branch.
  step. step. check "Hl". load_s32 "Hl" "Hmd". step. branch_rewrite (narrow_sgt md Hmd). step. branch.
  (* iw_1.L191: `c: _IO_UNBUFFERED`, or else the mode is 0. *)
  step. check "Hl". load_s32 "Hl" "Hfl". step. step.
  destruct (Z.eqb_spec (Z.land fl 2) 0) as [Hb | Hb].
  1: assert (md = 0) as -> by (destruct Hub as [Hub | Hub]; [contradiction | exact Hub]);
    branch_as false; step; step; check "Hl"; load_s32 "Hl" "Hmd"; step; step; step; branch.
  2: branch_as true; step; branch.
  (* iw_1.L291: the mode -1, and `c: _IO_USER_LOCK` clear. *)
  all: step; step; check "Hl"; store_int "Hl" "Hmd"; check "Hl"; load_s32 "Hl" "Hfl"; step; step; branch_as false.
  all: iApply ("HK" with "[%] Hl [Hfl] [Hmd] H80"); [split_and!; lk_prove | iSplit; done | iSplit; done].
Qed.

End rules.
