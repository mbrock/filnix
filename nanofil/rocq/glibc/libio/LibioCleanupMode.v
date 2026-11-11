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

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry LibioCleanupCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean LibioFlushStart
  LibioFlushTail LibioFlushBody LibioFlush LibioCleanupFpLock.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioCleanupModeOn (R : Runtime) (LG0 : LogicSig R).
Module CL := LibioCleanupFpLockOn R LG0.
Import CL CL.FA CL.FA.FB CL.FA.FB.FT CL.FA.FB.FT.FS CL.FA.FB.FT.FS.FC CL.FA.FB.FT.FS.FC.FU
  CL.FA.FB.FT.FS.FC.FU.FL CL.FA.FB.FT.FS.FC.FU.FL.CS CL.FA.FB.FT.FS.FC.FU.FL.CS.SW
  CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.FI.ML CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.FI.LG CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.FI.L
  CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.OW CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.FI CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance cleanup_mode_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A branch on a mode test, decided by the equation E. *)
Ltac fbrm E :=
  eapply step_wand; [eapply wp_branch; inst; vx |]; rewrite E;
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := vm_of c in change c with c' end; cbn [edge_label].

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
  fs. fs. fchk "Hl". fldn "Hl" "H80". fs. fs. fs. fbr.
  fs. fs. fchk "Hl". fldi "Hl" "Hmd". fs. fbrm (narrow_sgt md Hmd). fs. fbr.
  (* iw_1.L191: `c: _IO_UNBUFFERED`, or else the mode is 0. *)
  fs. fchk "Hl". fldi "Hl" "Hfl". fs. fs.
  destruct (Z.eqb_spec (Z.land fl 2) 0) as [Hb | Hb].
  1: assert (md = 0) as -> by (destruct Hub as [Hub | Hub]; [contradiction | exact Hub]);
    fbrv false; fs; fs; fchk "Hl"; fldi "Hl" "Hmd"; fs; fs; fs; fbr.
  2: fbrv true; fs; fbr.
  (* iw_1.L291: the mode -1, and `c: _IO_USER_LOCK` clear. *)
  all: fs; fs; fchk "Hl"; fsti "Hl" "Hmd"; fchk "Hl"; fldi "Hl" "Hfl"; fs; fs; brv false.
  all: iApply ("HK" with "[%] Hl [Hfl] [Hmd] H80"); [split_and!; lk_prove | iSplit; done | iSplit; done].
Qed.

End rules.
End LibioCleanupModeOn.
