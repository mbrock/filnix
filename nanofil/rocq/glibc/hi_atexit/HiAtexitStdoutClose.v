(** After nonempty string output, stdout owns a heap buffer even if
    the write failed. This file passes that buffer and the preserved
    stream fields to the proved close callback. The caller still
    supplies the actual stream list and thread cleanup resources. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  HiAtexitBase HiAtexitGe HiAtexitFclose HiAtexitCloseStdout HiAtexitOutputClose HiAtexitStdout.
Import ListNotations.
Open Scope Z_scope.
Import HP.PN.PB.PM.PC.PU.PL.
Import PI PI.CS PI.CS.SW PI.CS.SW.FI.ML PI.CS.SW.FI.LG PI.CS.SW.FI.L
  PI.CS.SW.OW PI.CS.SW.FI PI.CS.SW.ST.
Import HFC.FU.FT.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** Closing uses the linked program and its OS registry. *)
Local Instance hi_stdout_close_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** The output predicate supplies the allocated buffer, saved-buffer
    pointers and free lock. No successful byte count is required to
    establish the close callback's precondition. *)
Lemma hi_stdout_after_close s pre post fp eb vb vreg sb sreg fcp pin so soreg Φ :
  s <> [] ->
  lookup (TAtom "stdout") (ge_globals hge) = Some (mkPtr so (Obj so)) -> so mod 8 = 0 -> so + 8 <= r_end soreg ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals hge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals hge) = Some pin -> ptr_addr pin <> ptr_addr fp ->
  0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals hge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  vtables_ro hge vb vreg -∗ single_ro hge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live so soreg -∗ pcell so 0 fp -∗ hi_stdout_after w0 eb vb s fp None -∗
  io_list_inv hge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ io_list_inv hge (pre ++ post) -∗
     ([∗ list] g ∈ pre ++ post, stream_life g) -∗ Φ RetVoid) -∗
  WP (ERun hi_close_frame : sexpr) {{ Φ }}.
Proof.
  intros Hs Hgso Hsoal Hsoend Hgout Hgin Hin Hinr Hfc Hfcr Heb.
  iIntros "Hvt Hsingle Htcb Hso Hsoc Hf Hio Hlives HK".
  iDestruct "Hf" as (fb freg nb wp we lb (Hfp & Hfb & Hal & Hend & Hreg & Hlb & Hprogress))
    "(Hl & Hvtp & Hwb & Hxf & Htail)".
  subst fp. destruct nb as [[bb sz] |]; [|exfalso; exact (Hprogress Hs eq_refl)].
  iDestruct "Htail" as "(H72 & H80 & H96 & Hlp & Hlk)".
  iDestruct "Hlk" as (lb' lbreg Hlp) "Hlk". injection Hlp as <-.
  iApply (hi_output_close w0 pre post fb freg bb sz wp we eb vb vreg lb lbreg sb sreg fcp pin so soreg
    with "Hvt Hsingle Htcb Hso Hsoc Hl Hvtp Hwb Hxf H72 H80 H96 Hlp Hlk Hio Hlives HK"); try assumption.
Qed.

End rules.
