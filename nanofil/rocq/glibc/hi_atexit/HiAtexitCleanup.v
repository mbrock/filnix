(** After the close callback removes stdout, glibc cleans up the unused
    stdin and stderr streams. This file supplies the cleanup rule for
    the linked program, with its push, pop and flush callees discharged.
    The caller still owns the initialized thread and remaining streams. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics ExternalCalls Pieces Heap Logic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioFlushInv LibioCleanupExit
  HiAtexitBase HiAtexitFns HiAtexitGe HiAtexitCloseIt.
Import ListNotations.
Open Scope Z_scope.

(** Clients can describe remaining streams without loading a concrete
    copy of the entire flush proof chain. *)
Module HFL := LibioFlushInvOn InterpRuntime HLG.
Import HFL HFL.FI HLG HLG.L.

(** The interface exposes only the proved cleanup rule. Its implementation
    must discharge this rule; the interface adds no trusted assumption. *)
Module Type HiCleanupSig.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** The linked cleanup function accepts any remaining streams with
    nothing pending. Its function calls require no additional hypotheses. *)
Parameter hi_cleanup_rule : forall fs sb sreg fcp,
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals hge) = Some fcp ->
  0 <= ptr_addr fcp < 2 ^ 64 ->
  ⊢ HGV.ER.XL.XT.cleanup_rule w0 hge
    (single_ro hge sb sreg ∗ tcb_cleanup_inv (ow_self w0) ∗ io_list_inv hge fs ∗
      [∗ list] g ∈ fs, stream_life g ∗ exit_stream false g).

End rules.
End HiCleanupSig.

(** Sealing keeps the implementation's copied modules private while
    retaining the concrete proof of the public rule. *)
Module HC : HiCleanupSig.
Module HCE := LibioCleanupExitOn InterpRuntime HLG.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** The implementation supplies push, pop, flush and cleanup from the
    linked environment, with no callee rule left to the client. *)
Lemma hi_cleanup_rule fs sb sreg fcp :
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals hge) = Some fcp ->
  0 <= ptr_addr fcp < 2 ^ 64 ->
  ⊢ HGV.ER.XL.XT.cleanup_rule w0 hge
    (single_ro hge sb sreg ∗ tcb_cleanup_inv (ow_self w0) ∗ io_list_inv hge fs ∗
      [∗ list] g ∈ fs, stream_life g ∗ exit_stream false g).
Proof.
  intros Hfc Hfcr.
  exact (HCE.cleanup_rule_exit w0 hge (hi_sys_external _)
    (hi_find___GI___libc_cleanup_push_defer _) (hi_find___GI___libc_cleanup_pop_restore _)
    (hi_find___GI__IO_flush_all _) (hi_find__IO_cleanup _) fs sb sreg fcp Hfc Hfcr).
Qed.

End rules.
End HC.
Export HC.
