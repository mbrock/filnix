(** This file proves one pass of the loop of `c: _IO_unbuffer_all`,
    which is inlined in `c: _IO_cleanup` (LibioCleanupCode.v), over a
    stream that [exit_stream] describes. The pass runs from block `c: iw_1.L82` to
    the loop's head again. It sets `c: run_fp` to the stream and takes
    the stream's lock (LibioCleanupFpLock.v). It finds no backup area,
    keeps the buffer, since the stream is unbuffered or its mode is 0,
    and sets the mode to -1 (LibioCleanupMode.v). Then it releases the
    lock, clears `c: run_fp` and reads the next stream from
    `c: _chain` (LibioCleanupFpUnlock.v). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioFlushCode LibioCleanupCode FileInv
  LibioLogic SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean LibioFlushStart
  LibioFlushTail LibioFlushBody LibioFlush LibioCleanupFpLock LibioCleanupMode LibioCleanupFpUnlock
  LibioCleanupStart LibioCleanupLock.
From Glibc Require FileInv LibioCleanupFpLock LibioCleanupFpUnlock LibioCleanupLock LibioCleanupMode LibioCleanupStart LibioCloseSteps LibioFlush LibioFlushBody LibioFlushClean LibioFlushFpLock LibioFlushFpUnlock LibioFlushStart LibioFlushTail LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioCleanupLock LibioCleanupStart LibioCleanupFpUnlock LibioCleanupMode LibioCleanupFpLock LibioFlush LibioFlushBody LibioFlushTail LibioFlushStart LibioFlushClean LibioFlushFpUnlock LibioFlushFpLock LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance cleanup_pass_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A pass of `c: _IO_unbuffer_all`'s loop over the [exit_stream] fb
    in `c: iw_1.pr.1`, with `c: _chain` nx, from block `c: iw_1.L82`
    to the loop's head, entered from `c: iw_1.L301` with nx in
    `c: iw_1.v385`: the stream's mode is -1 after it, `c: run_fp` is
    null again, and the flush's result r in `c: v1` and the cleanup
    buffer in `c: iw_1.v2` are kept. *)
Lemma cleanup_pass e fb freg rf rfreg sb sreg r cb nx nreg Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  lookup (TAtom "iw_1.pr.1") e = Some (WPtr fp) -> lookup (TAtom "v1") e = Some (WInt r) ->
  lookup (TAtom "iw_1.v2") e = Some (WPtr cb) ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr nx < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  single_ro ge sb sreg -∗ live fb freg -∗ exit_stream false fp -∗ live rf rfreg -∗ pcell rf 0 null -∗
  pcell fb off_chain nx -∗ live_cap (ptr_cap nx) nreg -∗
  (∀ e', ⌜lookup (TAtom "iw_1.v385") e' = Some (WPtr nx) /\ lookup (TAtom "v1") e' = Some (WInt r) /\
          lookup (TAtom "iw_1.v2") e' = Some (WPtr cb)⌝ -∗
     live fb freg -∗ exit_stream true fp -∗ live rf rfreg -∗ pcell rf 0 null -∗ pcell fb off_chain nx -∗
     live_cap (ptr_cap nx) nreg -∗
     WP (ERun (mkFrame glibc__IO_cleanup e' [] None (Enter (TAtom "iw_1.L81") (Some (TAtom "iw_1.L301"))))
          : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_cleanup e [] None (Enter (TAtom "iw_1.L82") (Some (TAtom "iw_1.L81")))) : sexpr)
    {{ Φ }}.
Proof.
  intros fp Hgrf Hp1 Hv1 Hv2 Hsz Hnx Hfb Hfal Hfend Hfreg Hral Hrend.
  iIntros "#Hs Hl HX Hrl Hrc Hnc Hnl HK".
  iDestruct "HX" as (fb' fl f2 fd md lb lbreg c breg arp are awb awp Hx)
    "(Hfl & Hf2 & Hfd & Hmd & Hlp & Hlk & H8 & H16 & H32 & H40 & Hcl & H80)".
  destruct Hx as (Heq & Hfl & Hfl15 & Hf2 & Hfd & Hw & Hwb & Hrd & Hrb & Hmd & Hmu). injection Heq as <-.
  iApply (wp_cleanup_L82 w0 registry ge Hreg Hext e fb freg fl lb lbreg rf rfreg sb sreg null r cb
            with "Hs Hl Hfl Hlp Hlk Hrl Hrc"); try assumption.
  iNext. iIntros (e1 (Hp1' & Hc13 & Hv1' & Hv2')) "Hl Hfl Hlp Hlk Hrl Hrc".
  iApply (wp_cleanup_L93 w0 registry ge e1 fb freg fl md r cb with "Hl Hfl Hmd H80"); try assumption.
  iNext. iIntros (e2 (Hp1'' & Hc13' & Hv1'' & Hv2'')) "Hl Hfl Hmd H80".
  iApply (wp_cleanup_L306 w0 registry ge e2 r fb freg lb lbreg rf rfreg sb sreg _ cb nx nreg
            with "Hs Hl Hlp Hlk Hrl Hrc Hnc Hnl"); try assumption.
  iNext. iIntros (e3 Hv) "Hl Hlp Hlk Hrl Hrc Hnc Hnl".
  iApply ("HK" $! e3 Hv with "Hl [-Hrl Hrc Hnc Hnl] Hrl Hrc Hnc Hnl").
  iExists fb, fl, f2, fd, (2 ^ 32 - 1), lb, lbreg, c, breg, arp, are, awb, awp. iFrame. iPureIntro.
  split_and!; auto; lia.
Qed.

End rules.
