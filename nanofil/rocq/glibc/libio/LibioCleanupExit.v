From Glibc Require Import GlibcProgram.
(** This file shows that `c: _IO_cleanup ()` behaves at exit as
    ExitRunTail.v's [cleanup_rule] says, for the streams still open,
    with no premise left about the functions it calls.

    LibioCleanup.v proves the function over two premises,
    `c: __libc_cleanup_push_defer`'s and
    `c: __libc_cleanup_pop_restore`'s triples for a buffer at offset 0
    ([push_spec], [pop_spec]). This file proves both from SysCleanup.v
    and SysCleanupPop.v ([push_spec_holds], [pop_spec_holds]), so
    [wp_glibc__IO_cleanup_exit] needs only the functions ge defines.
    [cleanup_rule_io] is [cleanup_rule] over any streams whose flush
    leaves [exit_stream]s, and [cleanup_rule_exit] is it for
    [exit_stream]s themselves, as the unused `c: stdin` and the
    unbuffered `c: stderr` are after `c: close_stdout`. *)

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
  LibioCleanupStart LibioCleanupLock LibioCleanupPass LibioCleanup SysCleanup SysCleanupPop ExitRunTail.
From Glibc Require ExitRunTail FileInv LibioCleanup LibioCleanupFpLock LibioCleanupFpUnlock LibioCleanupLock LibioCleanupMode LibioCleanupPass LibioCleanupStart LibioCloseSteps LibioFlush LibioFlushBody LibioFlushStart LibioFlushTail LibioLogic OsWorld SysCleanup SysCleanupPop SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


Import LibioCleanup LibioCleanupPass LibioCleanupLock LibioCleanupStart LibioCleanupFpUnlock LibioCleanupMode LibioCleanupFpLock LibioFlush LibioFlushBody LibioFlushTail LibioFlushStart LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** [push_spec] holds: it is SysCleanup.v's triple at offset 0. *)
Lemma push_spec_holds : push_spec w0 registry ge.
Proof.
  intros fr cb creg pv xs Φ Hfr Hcb Hcal Hcend Hcreg Hxs.
  iIntros "Htcb Hcl Hc24 Hc16 HK".
  iApply (SysCleanup.wp_glibc___libc_cleanup_push_defer Hreg Hext fr cb creg 0 pv xs
            with "Htcb Hcl Hc24 Hc16");
    [rewrite Z.add_0_r; exact Hfr | lia | lia | rewrite Z.add_0_r; exact Hcal | lia | lia | exact Hxs |].
  iNext. iIntros "Htcb Hcl Hc24 Hc16". iEval (rewrite Z.add_0_r) in "Htcb".
  iApply ("HK" with "Htcb Hcl Hc24 Hc16").
Qed.

(** [pop_spec] holds: it is SysCleanupPop.v's triple at offset 0. *)
Lemma pop_spec_holds : pop_spec w0 registry ge.
Proof.
  intros fr cb creg Φ Hfr Hcb Hcal Hcend Hcreg.
  iIntros "Htcb Hcl Hcp Hct HK".
  assert (E : mkPtr cb (Obj cb) = mkPtr (cb + 0) (Obj cb)) by (rewrite Z.add_0_r; reflexivity).
  iEval (rewrite E) in "Htcb".
  iApply (SysCleanupPop.wp_glibc___libc_cleanup_pop_restore Hreg Hext fr cb creg 0
            with "Htcb Hcl Hcp Hct");
    [rewrite Z.add_0_r; exact Hfr | lia | lia | rewrite Z.add_0_r; exact Hcal | lia | lia |].
  iNext. iIntros "Htcb Hcl Hcp Hct". iApply ("HK" with "Htcb Hcl Hcp Hct").
Qed.

(** LibioCleanup.v's [wp_glibc__IO_cleanup], its premises about the
    cleanup buffer's push and pop discharged: what is left is that ge
    defines the callees as glibc does. *)
Lemma wp_glibc__IO_cleanup_exit fr (P : ptr -> iProp Σ) fs sb sreg fcp Φ :
  find_fn ge (TAtom "__GI___libc_cleanup_push_defer") = Some (Defined glibc___libc_cleanup_push_defer) ->
  find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") = Some (Defined glibc___libc_cleanup_pop_restore) ->
  find_fn ge (TAtom "__GI__IO_flush_all") = Some (Defined glibc__IO_flush_all) ->
  flush_body w0 registry ge P (exit_stream false) -> call_frame glibc__IO_cleanup [] = Some fr ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge fs -∗
  ([∗ list] g ∈ fs, stream_life g ∗ P g) -∗
  ▷ (∀ r, ⌜r = 0 \/ r = 2 ^ 32 - 1⌝ -∗ tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge fs -∗
     ([∗ list] g ∈ fs, stream_life g ∗ exit_stream true g) -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hpush Hpop Hflush. apply (wp_glibc__IO_cleanup Hreg Hext).
  - exact push_spec_holds.
  - exact pop_spec_holds.
Qed.

End rules.

Section exit.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (Hext : sys_external ge).
Context (Hpush : find_fn ge (TAtom "__GI___libc_cleanup_push_defer") =
                 Some (Defined glibc___libc_cleanup_push_defer)).
Context (Hpop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") =
                Some (Defined glibc___libc_cleanup_pop_restore)).
Context (Hflush : find_fn ge (TAtom "__GI__IO_flush_all") = Some (Defined glibc__IO_flush_all)).
Context (Hcl : find_fn ge (TAtom "_IO_cleanup") = Some (Defined glibc__IO_cleanup)).

(** The Iris instance of user glibc's OS registry and world, as
    ExitRunTail.v's. *)
Local Instance cleanup_rule_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** [glibc_os_registry] holds its own contracts. *)
Lemma holds_os_glibc : holds_os glibc_os_registry.
Proof. intros n c H. exact H. Qed.

(** ExitRunTail.v's [cleanup_rule] for the streams fs of
    [io_list_inv], each with its life and P, whose flush is the
    [flush_body] from P to an [exit_stream], with the thread's cleanup
    fields and `c: __libc_single_threaded` set. *)
Lemma cleanup_rule_io (P : ptr -> iProp Σ) fs sb sreg fcp :
  flush_body w0 glibc_os_registry ge P (exit_stream false) ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  ⊢ ExitRunTail.cleanup_rule w0 ge (single_ro ge sb sreg ∗ tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge fs ∗
                           [∗ list] g ∈ fs, stream_life g ∗ P g).
Proof.
  intros Hbody Hfc Hfcr. iIntros (f e ls lab d rest j Ψ) "(#Hs & Htcb & Hio & Hfs) HK".
  iApply wp_call_bind; [reflexivity | exact Hcl | reflexivity |]. iNext.
  iApply (wp_glibc__IO_cleanup_exit (glibc_program := program_of w0 glibc_os_registry ge) holds_os_glibc Hext with "Hs Htcb Hio Hfs");
    [exact Hpush | exact Hpop | exact Hflush | exact Hbody | reflexivity | exact Hfc | exact Hfcr |].
  iNext. iIntros (r Hr) "_ _ _". resume. iApply "HK".
Qed.

(** [cleanup_rule_io] for streams that are [exit_stream]s already,
    with nothing to flush ([flush_body_exit]). *)
Lemma cleanup_rule_exit fs sb sreg fcp :
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  ⊢ ExitRunTail.cleanup_rule w0 ge (single_ro ge sb sreg ∗ tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge fs ∗
                           [∗ list] g ∈ fs, stream_life g ∗ exit_stream false g).
Proof.
  intros Hfc Hfcr. apply (cleanup_rule_io (exit_stream false) fs sb sreg fcp); [|exact Hfc | exact Hfcr].
  apply (flush_body_exit (glibc_program := program_of w0 glibc_os_registry ge) holds_os_glibc Hext).
Qed.

End exit.
