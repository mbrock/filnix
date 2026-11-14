From Glibc Require Import GlibcProgram.
(** The start of one pass of the loop of `c: _IO_unbuffer_all`, which
    `c: _IO_cleanup` inlines after `c: _IO_flush_all`
    (LibioCleanupCode.v), from block `c: iw_1.L82`: the pass sets
    `c: run_fp` to the stream and takes the stream's lock, as
    LibioFlushFpLock.v does in `c: _IO_flush_all`. Block
    `c: iw_1.L93` then looks at the stream's backup area and buffer
    (LibioCleanupMode.v). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry LibioCleanupCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFlushFpLock
  LibioFlushFpUnlock LibioFlushClean LibioFlushStart LibioFlushTail LibioFlushBody LibioFlush.
From Glibc Require FileInv LibioCloseSteps LibioFlush LibioFlushBody LibioFlushClean LibioFlushFpLock LibioFlushFpUnlock LibioFlushStart LibioFlushTail LibioLogic OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioFlush LibioFlushBody LibioFlushTail LibioFlushStart LibioFlushClean LibioFlushFpUnlock LibioFlushFpLock LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The premises of `c: zthread_self_cookie`'s rule. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** A call of `c: zthread_self_cookie`, whose result is the thread's
    cookie, not null (H). *)
Ltac self H := iApply (OsThread.wp_zthread_self_cookie); try self_side; [exact H|]; iNext.

(** Block `c: iw_1.L82` of `c: _IO_cleanup` to block `c: iw_1.L93`,
    the stream fb in `c: iw_1.pr.1`: `c: run_fp` becomes fb, and the
    stream's free lock lb is taken by the thread, count 0. The flush's
    result r in `c: v1` and the cleanup buffer in `c: iw_1.v2` are
    kept, and `c: chk13` holds the stream. *)
Lemma wp_cleanup_L82 e fb freg fl lb lbreg rf rfreg sb sreg x r cb Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  lookup (TAtom "iw_1.pr.1") e = Some (WPtr fp) -> lookup (TAtom "v1") e = Some (WInt r) ->
  lookup (TAtom "iw_1.v2") e = Some (WPtr cb) ->
  ptr_addr (ow_self w0) <> 0 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 -> rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗ live rf rfreg -∗ pcell rf 0 x -∗
  ▷ (∀ e', ⌜lookup (TAtom "iw_1.pr.1") e' = Some (WPtr fp) /\ lookup (TAtom "chk13") e' = Some (WPtr fp) /\
            lookup (TAtom "v1") e' = Some (WInt r) /\ lookup (TAtom "iw_1.v2") e' = Some (WPtr cb)⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
     lock_state lb lbreg 1 0 (ow_self w0) -∗ live rf rfreg -∗ pcell rf 0 fp -∗
     WP (ERun (mkFrame glibc__IO_cleanup e' [] None
          (Enter (TAtom "iw_1.L93") (Some (TAtom "iw_1.L103")))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_cleanup e [] None (Enter (TAtom "iw_1.L82") (Some (TAtom "iw_1.L81")))) : sexpr)
    {{ Φ }}.
Proof.
  intros fp Hgrf Hp1 Hv1 Hv2 Hsz Hfb Hfal Hfend Hfreg Hfl Hul Hral Hrend. subst fp.
  unfold file_size in Hfend. assert (0 <= Z.land fl 32768 < 2 ^ 32) by (rewrite Hul; lia).
  iIntros "#Hs Hl [_ Hfl] Hlp Hlb Hrl Hrc HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlb" as "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
  iApply (wp_live_fit1 with "Hrl"). iIntros ([Hrf0 Hrf48]) "Hrl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  (* iw_1.L82: `c: run_fp`, and `c: _IO_USER_LOCK` clear. *)
  step. step. check "Hrl". store "Hrl" "Hrc". check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  (* iw_1.L98, iw_1.L109, iw_1.L110: single threaded, the owner null. *)
  step. self Hsz. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". load_null "Hbl" "Hbo". step. step. step. step. step. branch.
  (* iw_1.L103: the lock word 1, the owner the cookie. *)
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl". store_int "Hbl" "Hb0". load "Hl" "Hlp" "Hbl". step.
  check "Hbl". store "Hbl" "Hbo". step.
  iApply ("HK" with "[%] Hl [Hfl] Hlp [Hbl Hb0 Hb4 Hbo] Hrl Hrc").
  - split_and!; lk_prove.
  - iSplit; [done | iExact "Hfl"].
  - iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
Qed.

End rules.
