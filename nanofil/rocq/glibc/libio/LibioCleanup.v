From Glibc Require Import GlibcProgram.
(** This file proves `c: _IO_cleanup ()` (LibioCleanupCode.v,
    libio/genops.c), which `c: exit` calls after the atexit handlers
    to flush and unbuffer every open stream.

    The function calls `c: _IO_flush_all` (LibioFlush.v), pushes a
    cleanup buffer (LibioCleanupStart.v) and takes `c: list_all_lock`
    (LibioCleanupLock.v). Then it runs the inlined loop of
    `c: _IO_unbuffer_all` over the streams of [io_list_inv]'s list,
    one pass per stream ([cleanup_loop], by induction on the list).
    Each pass sets `c: run_fp` and takes the stream's lock
    (LibioCleanupFpLock.v). It finds no backup area and keeps the
    buffer, since the stream is unbuffered or its mode is 0, and sets
    the mode to -1 (LibioCleanupMode.v). Then it releases the lock and
    clears `c: run_fp` (LibioCleanupFpUnlock.v). After the loop the
    function releases the list's lock, pops the buffer and returns the
    flush's result ([wp_glibc__IO_cleanup]).

    The streams at exit are [exit_stream]s: after `c: close_stdout`
    has closed `c: stdout`, the unused `c: stdin` and the unbuffered
    `c: stderr` have nothing to flush. [cleanup_rule_io] is
    ExitRunTail.v's [cleanup_rule] for them. *)

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
  LibioCleanupStart LibioCleanupLock LibioCleanupPass.
From Glibc Require FileInv LibioCleanupFpLock LibioCleanupFpUnlock LibioCleanupLock LibioCleanupMode LibioCleanupPass LibioCleanupStart LibioCloseSteps LibioFlush LibioFlushBody LibioFlushClean LibioFlushFpLock LibioFlushFpUnlock LibioFlushStart LibioFlushTail LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioCleanupPass LibioCleanupLock LibioCleanupStart LibioCleanupFpUnlock LibioCleanupMode LibioCleanupFpLock LibioFlush LibioFlushBody LibioFlushTail LibioFlushStart LibioFlushClean LibioFlushFpUnlock LibioFlushFpLock LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context `{Hpush : !Defines ge "__GI___libc_cleanup_push_defer" glibc___libc_cleanup_push_defer}.
Context `{Hpop : !Defines ge "__GI___libc_cleanup_pop_restore" glibc___libc_cleanup_pop_restore}.
Context `{Hflush : !Defines ge "__GI__IO_flush_all" glibc__IO_flush_all}.
Context (Hpush_spec : push_spec w0 registry ge)
  (Hpop_spec : pop_spec w0 registry ge).


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The loop of `c: _IO_unbuffer_all` in `c: _IO_cleanup` from its
    head `c: iw_1.L81`, over the streams rest still to pass, linked
    from prev, each an [exit_stream] not yet passed: the head is
    entered from `c: iw_1.L14` with rest's first stream in
    `c: iw_1.v80`, or from `c: iw_1.L301` with it in `c: iw_1.v385`.
    Each pass sets the stream's mode to -1, and block `c: iw_1.L386`
    is entered with every stream passed, the flush's result r in
    `c: v1` and the cleanup buffer in `c: iw_1.v2` kept. *)
Lemma cleanup_loop rest prev e from r cb rf rfreg sb sreg Φ :
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  rf mod 8 = 0 -> rf + 8 <= r_end rfreg -> ptr_addr (ow_self w0) <> 0 ->
  (from = TAtom "iw_1.L14" /\ lookup (TAtom "iw_1.v80") e = Some (WPtr (head_ptr rest))) \/
  (from = TAtom "iw_1.L301" /\ lookup (TAtom "iw_1.v385") e = Some (WPtr (head_ptr rest))) ->
  lookup (TAtom "v1") e = Some (WInt r) -> lookup (TAtom "iw_1.v2") e = Some (WPtr cb) ->
  single_ro ge sb sreg -∗ live rf rfreg -∗ pcell rf 0 null -∗ chain_links prev rest -∗
  ([∗ list] g ∈ rest, stream_life g ∗ exit_stream false g) -∗
  (∀ e', ⌜lookup (TAtom "v1") e' = Some (WInt r) /\ lookup (TAtom "iw_1.v2") e' = Some (WPtr cb)⌝ -∗
     live rf rfreg -∗ pcell rf 0 null -∗ chain_links prev rest -∗
     ([∗ list] g ∈ rest, stream_life g ∗ exit_stream true g) -∗
     WP (ERun (mkFrame glibc__IO_cleanup e' [] None (Enter (TAtom "iw_1.L386") (Some (TAtom "iw_1.L81"))))
          : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_cleanup e [] None (Enter (TAtom "iw_1.L81") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hgrf Hral Hrend Hsz. revert prev e from.
  induction rest as [|g rest IH]; intros prev e from Hph Hv1 Hv2; cbn [head_ptr] in Hph.
  - iIntros "#Hs Hrl Hrc Hch Hfs HK".
    destruct Hph as [(-> & Hv) | (-> & Hv)].
    all: step; step; step; branch; iApply ("HK" with "[%] Hrl Hrc Hch Hfs"); split_and!; lk_prove.
  - iIntros "#Hs Hrl Hrc Hch Hfs HK". cbn [chain_links].
    iDestruct "Hch" as (gb ->) "(Hpv & Hnc & Hch)".
    iDestruct "Hfs" as "[[(%gb' & %greg & %Hg & Hl) HX] Hfs]".
    destruct Hg as (Heq & Hgb & Hgal & Hgend & Hgreg). injection Heq as <-. unfold file_size in Hgend.
    iDestruct (head_life with "Hfs") as (nreg Hnx) "[Hnl Hback]".
    iAssert (∀ e0, ⌜lookup (TAtom "iw_1.pr.1") e0 = Some (WPtr (mkPtr gb (Obj gb))) /\
                    lookup (TAtom "v1") e0 = Some (WInt r) /\ lookup (TAtom "iw_1.v2") e0 = Some (WPtr cb)⌝ -∗
      WP (ERun (mkFrame glibc__IO_cleanup e0 [] None (Enter (TAtom "iw_1.L82") (Some (TAtom "iw_1.L81"))))
           : sexpr) {{ Φ }})%I with "[-]" as "Hpass".
    { iIntros (e0 (Hp1 & Hv1' & Hv2')).
      iApply (cleanup_pass Hreg Hext with "Hs Hl HX Hrl Hrc Hnc Hnl");
        try first [exact Hp1 | exact Hv1' | exact Hv2' | exact Hgrf | exact Hsz | exact Hnx | exact Hral | exact Hrend | lia
                  | unfold file_size; lia].
      iIntros (e3 (Hv385 & Hv1t & Hv2t)) "Hl HX Hrl Hrc Hnc Hnl".
      iDestruct ("Hback" with "Hnl") as "Hfs".
      iApply (IH (mkPtr (gb + off_chain) (Obj gb)) e3 (TAtom "iw_1.L301") with "Hs Hrl Hrc Hch Hfs");
        [right; split; [reflexivity | exact Hv385] | exact Hv1t | exact Hv2t |].
      iIntros (e4 (Hv1f & Hv2f)) "Hrl Hrc Hch Hfs".
      iApply ("HK" $! e4 with "[%] Hrl Hrc [Hpv Hnc Hch] [-]"); [split; assumption | iExists gb; iFrame; done |].
      rewrite big_sepL_cons. iFrame "Hfs HX". iExists gb, greg. iFrame "Hl". iPureIntro.
      unfold file_size. split_and!; auto; lia. }
    destruct Hph as [(-> & Hv) | (-> & Hv)].
    all: step; step; step; branch_as false; iApply "Hpass"; iPureIntro; split_and!; lk_prove.
Qed.

(** `c: _IO_cleanup ()` over [io_list_inv]'s streams fs, each with
    its life and P, each pass of `c: _IO_flush_all` the
    [flush_body] from P to an [exit_stream] not yet unbuffered, the
    thread's cleanup fields as [tcb_cleanup_inv] says and
    `c: __libc_single_threaded` set: the function returns the flush's
    result, 0 or EOF, with the list as it was, every stream's mode -1,
    and the cleanup fields restored. *)
Lemma wp_glibc__IO_cleanup fr (P : ptr -> iProp Σ) fs sb sreg fcp Φ :
  flush_body w0 registry ge P (exit_stream false) -> call_frame glibc__IO_cleanup [] = Some fr ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge fs -∗
  ([∗ list] g ∈ fs, stream_life g ∗ P g) -∗
  ▷ (∀ r, ⌜r = 0 \/ r = 2 ^ 32 - 1⌝ -∗ tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge fs -∗
     ([∗ list] g ∈ fs, stream_life g ∗ exit_stream true g) -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hbody Hfr Hfc Hfcr.
  iIntros "#Hs Htcb Hio Hfs HK".
  iApply (wp_cleanup_start Hreg Hext Hpush_spec Hpop_spec
            with "Hs Htcb Hio Hfs"); [exact Hbody | exact Hfr | exact Hfc | exact Hfcr |].
  iNext. iIntros (e r cb creg la lareg lk lkreg rf rfreg Hpre) "Htcb Hcl Hc24 Hc16 Hla Hlah Hch Hlk Hrl Hrc Hfs".
  destruct Hpre as (Hv16 & Hv1 & Hv2 & Hr & Hcb & Hcal & Hcend & Hcreg & Hgla & Hglk & Hgrf & Hlaal & Hlaend &
                    Hral & Hrend & Hsz).
  iDestruct (head_life with "Hfs") as (hreg Hh) "[Hhl Hback]".
  iApply (wp_cleanup_L23 with "Hla Hlah Hhl Hlk"); try eassumption.
  iNext. iIntros (e1 (Hv80 & Hv1' & Hv2')) "Hla Hlah Hhl Hlk".
  iDestruct ("Hback" with "Hhl") as "Hfs".
  iApply (cleanup_loop fs (mkPtr la (Obj la)) e1 (TAtom "iw_1.L14") with "Hs Hrl Hrc Hch Hfs");
    [exact Hgrf | exact Hral | exact Hrend | exact Hsz | left; auto | exact Hv1' | exact Hv2' |].
  iIntros (e2 (Hv1'' & Hv2'')) "Hrl Hrc Hch Hfs".
  iApply (wp_cleanup_L386 Hpop_spec with "Hs Hlk Htcb Hcl Hc24 Hc16");
    try first [eassumption | destruct Hr as [-> | ->]; lia].
  iNext. iIntros "Hlk Htcb Hcl".
  iApply ("HK" $! r with "[%] Htcb [Hla Hlah Hch Hlk Hrl Hrc] Hfs"); [exact Hr|].
  iExists la, lareg, lk, lkreg, rf, rfreg. iFrame. iPureIntro. split_and!; assumption.
Qed.

End rules.
