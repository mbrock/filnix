From Glibc Require Import GlibcProgram.
(** The end of one pass of `c: _IO_unbuffer_all`'s loop in
    `c: _IO_cleanup` (LibioCleanupCode.v), from block `c: iw_1.L306`:
    as at the end of a pass of `c: _IO_flush_all`
    (LibioFlushFpUnlock.v), the pass releases the stream's lock, held
    once at count 0, clears `c: run_fp` and reads the stream's
    `c: _chain`, and the loop goes back to its head `c: iw_1.L81`.

    Reading `c: _chain` loads a pointer, which needs the life of the
    object it names: the next stream's, given as [live_cap], or
    nothing for null. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry LibioCleanupCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean LibioFlushStart
  LibioFlushTail LibioFlushBody LibioFlush LibioCleanupFpLock LibioCleanupMode.
From Glibc Require FileInv LibioCleanupFpLock LibioCleanupMode LibioCloseSteps LibioFlush LibioFlushBody LibioFlushClean LibioFlushFpLock LibioFlushFpUnlock LibioFlushStart LibioFlushTail LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioCleanupMode LibioCleanupFpLock LibioFlush LibioFlushBody LibioFlushTail LibioFlushStart LibioFlushClean LibioFlushFpUnlock LibioFlushFpLock LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: iw_1.L306` of `c: _IO_cleanup`, entered from
    `c: iw_1.L291`, to the loop's head: the stream's lock, held once
    by the thread, is released, `c: run_fp` is null again, and the
    head is entered with the next stream nx in `c: iw_1.v385`. The
    flush's result r in `c: v1` and the cleanup buffer in
    `c: iw_1.v2` are kept. *)
Lemma wp_cleanup_L306 e r fb freg lb lbreg rf rfreg sb sreg x cb nx nreg Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  lookup (TAtom "iw_1.pr.1") e = Some (WPtr fp) -> lookup (TAtom "chk13") e = Some (WPtr fp) ->
  lookup (TAtom "v1") e = Some (WInt r) -> lookup (TAtom "iw_1.v2") e = Some (WPtr cb) ->
  0 <= ptr_addr nx < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  single_ro ge sb sreg -∗ live fb freg -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 1 0 (ow_self w0) -∗ live rf rfreg -∗ pcell rf 0 x -∗
  pcell fb off_chain nx -∗ live_cap (ptr_cap nx) nreg -∗
  ▷ (∀ e', ⌜lookup (TAtom "iw_1.v385") e' = Some (WPtr nx) /\ lookup (TAtom "v1") e' = Some (WInt r) /\
            lookup (TAtom "iw_1.v2") e' = Some (WPtr cb)⌝ -∗
     live fb freg -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
     lock_state lb lbreg 0 0 null -∗ live rf rfreg -∗ pcell rf 0 null -∗
     pcell fb off_chain nx -∗ live_cap (ptr_cap nx) nreg -∗
     WP (ERun (mkFrame glibc__IO_cleanup e' [] None (Enter (TAtom "iw_1.L81") (Some (TAtom "iw_1.L301"))))
          : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_cleanup e [] None (Enter (TAtom "iw_1.L306") (Some (TAtom "iw_1.L291"))))
       : sexpr) {{ Φ }}.
Proof.
  intros fp Hgrf Hp1 Hc13 Hv1 Hv2 Hnx Hfb Hfal Hfend Hfreg Hral Hrend. subst fp.
  unfold file_size in Hfend.
  iIntros "#Hs Hl Hlp Hlb Hrl Hrc Hch Hnl HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlb" as "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
  iApply (wp_live_fit1 with "Hrl"). iIntros ([Hrf0 Hrf48]) "Hrl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  (* iw_1.L306: single threaded. *)
  step. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  (* iw_1.L315, iw_1.L316: the count is 0. *)
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". load_s32 "Hbl" "Hb4". step. step. step. branch.
  (* iw_1.L309: the owner null, then the lock word 0. *)
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". store "Hbl" "Hbo".
  check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl". store_int "Hbl" "Hb0". step.
  (* iw_1.L301: `c: run_fp` null, and the next stream. *)
  step. step. check "Hrl". store "Hrl" "Hrc". step. check "Hl". load "Hl" "Hch" "Hnl". step.
  iApply ("HK" with "[%] Hl Hlp [Hbl Hb0 Hb4 Hbo] Hrl Hrc Hch Hnl").
  - split_and!; lk_prove.
  - iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
Qed.

End rules.
