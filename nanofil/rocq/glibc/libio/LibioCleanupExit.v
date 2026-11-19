From Glibc Require Import Unit_libio_genops_os Unit_nptl_libcZ2dcleanup_os.
From Glibc Require Import GlibcProgram.
(** Process exit flushes and cleans up the streams that remain open.
    This file connects that operation to the exit handler's cleanup contract.
    It discharges the cleanup-buffer premises using the proved push and pop functions.

    The caller supplies the linked function bindings and ownership of the stream list.
    Cleanup supports both streams with pending output and streams that have nothing to flush. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry FileInv
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


(** The expression type uses this caller's linked program and registry. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Pushing a cleanup buffer satisfies the stream traversal's contract at offset zero. *)
Lemma push_spec_holds : push_spec w0 registry ge.
Proof using Type*.
  intros fr cb creg pv xs Φ Hfr Hcb Hcal Hcend Hcreg Hxs.
  iIntros "Htcb Hcl Hc24 Hc16 HK".
  iApply (SysCleanup.wp_glibc___libc_cleanup_push_defer Hreg Hext fr cb creg 0 pv xs
            with "Htcb Hcl Hc24 Hc16");
    [rewrite Z.add_0_r; exact Hfr | lia | lia | rewrite Z.add_0_r; exact Hcal | lia | lia | exact Hxs |].
  iNext. iIntros "Htcb Hcl Hc24 Hc16". iEval (rewrite Z.add_0_r) in "Htcb".
  iApply ("HK" with "Htcb Hcl Hc24 Hc16").
Qed.

(** Popping that buffer restores the thread's cleanup state at offset zero. *)
Lemma pop_spec_holds : pop_spec w0 registry ge.
Proof using Type*.
  intros fr cb creg Φ Hfr Hcb Hcal Hcend Hcreg.
  iIntros "Htcb Hcl Hcp Hct HK".
  assert (E : mkPtr cb (Obj cb) = mkPtr (cb + 0) (Obj cb)) by (rewrite Z.add_0_r; reflexivity).
  iEval (rewrite E) in "Htcb".
  iApply (SysCleanupPop.wp_glibc___libc_cleanup_pop_restore Hreg Hext fr cb creg 0
            with "Htcb Hcl Hcp Hct");
    [rewrite Z.add_0_r; exact Hfr | lia | lia | rewrite Z.add_0_r; exact Hcal | lia | lia |].
  iNext. iIntros "Htcb Hcl Hcp Hct". iApply ("HK" with "Htcb Hcl Hcp Hct").
Qed.

(** Cleanup flushes the stream list and restores the thread's cleanup fields.
    The linked functions discharge the traversal's buffer-management premises. *)
Lemma wp_glibc__IO_cleanup_exit fr (P : ptr -> iProp Σ) fs sb sreg fcp Φ :
  find_fn ge (TAtom "__GI___libc_cleanup_push_defer") = Some (Defined Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer) ->
  find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") = Some (Defined Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore) ->
  find_fn ge (TAtom "__GI__IO_flush_all") = Some (Defined Unit_libio_genops_os.fn___GI__IO_flush_all) ->
  flush_body w0 registry ge P (exit_stream false) -> call_frame Unit_libio_genops_os.fn__IO_cleanup [] = Some fr ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge fs -∗
  ([∗ list] g ∈ fs, stream_life g ∗ P g) -∗
  ▷ (∀ r, ⌜r = 0 \/ r = 2 ^ 32 - 1⌝ -∗ tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge fs -∗
     ([∗ list] g ∈ fs, stream_life g ∗ exit_stream true g) -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hpush Hpop Hflush. apply (wp_glibc__IO_cleanup Hreg Hext).
  - exact push_spec_holds.
  - exact pop_spec_holds.
Qed.

End rules.

Section exit.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (Hext : sys_external ge).
Context (Hpush : Defines ge "__GI___libc_cleanup_push_defer" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer).
Context (Hpop : Defines ge "__GI___libc_cleanup_pop_restore" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore).
Context (Hflush : Defines ge "__GI__IO_flush_all" Unit_libio_genops_os.fn___GI__IO_flush_all).
Context (Hcl : Defines ge "_IO_cleanup" Unit_libio_genops_os.fn__IO_cleanup).
Existing Instances Hpush Hpop Hflush Hcl.

(** The state interpretation connects cleanup execution to the OS world and registry. *)
Local Instance cleanup_rule_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** [glibc_os_registry] holds its own contracts. *)
Lemma holds_os_glibc : holds_os glibc_os_registry.
Proof using Type*. intros n c H. exact H. Qed.

(** Cleanup consumes the stream list after flushing each stream into its exit state.
    The caller supplies the thread's cleanup fields and the single-threaded flag. *)
Lemma cleanup_rule_io (P : ptr -> iProp Σ) fs sb sreg fcp :
  flush_body w0 glibc_os_registry ge P (exit_stream false) ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  ⊢ ExitRunTail.cleanup_rule w0 ge (single_ro ge sb sreg ∗ tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge fs ∗
                           [∗ list] g ∈ fs, stream_life g ∗ P g).
Proof using Hcl Hext Hflush Hpop Hpush.
  intros Hbody Hfc Hfcr. iIntros (f e ls lab d rest j Ψ) "(#Hs & Htcb & Hio & Hfs) HK".
  iApply wp_call_bind; [reflexivity | exact Hcl | reflexivity |]. iNext.
  iApply (wp_glibc__IO_cleanup_exit (glibc_program := program_of w0 glibc_os_registry ge) holds_os_glibc Hext with "Hs Htcb Hio Hfs");
    [exact Hpush | exact Hpop | exact Hflush | exact Hbody | reflexivity | exact Hfc | exact Hfcr |].
  iNext. iIntros (r Hr) "_ _ _". resume. iApply "HK".
Qed.

(** Streams already in their exit state satisfy the same cleanup rule without further output. *)
Lemma cleanup_rule_exit fs sb sreg fcp :
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  ⊢ ExitRunTail.cleanup_rule w0 ge (single_ro ge sb sreg ∗ tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge fs ∗
                           [∗ list] g ∈ fs, stream_life g ∗ exit_stream false g).
Proof using Hcl Hext Hflush Hpop Hpush.
  intros Hfc Hfcr. apply (cleanup_rule_io (exit_stream false) fs sb sreg fcp); [|exact Hfc | exact Hfcr].
  apply (flush_body_exit (glibc_program := program_of w0 glibc_os_registry ge) holds_os_glibc Hext).
Qed.

End exit.
