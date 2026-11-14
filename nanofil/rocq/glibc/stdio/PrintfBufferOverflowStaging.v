(** Flushing a staged character updates printf's count before calling the
    stream's overflow routine. EOF marks failure; any other result proceeds
    to buffer selection with the original character still owned.

    This proof connects the function entry to both caller outcomes.
    The overflow contract and the subsequent buffer selection remain explicit
    obligations, so the proof does not assume that output succeeds. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode PrintfBufferFileCode PrintfBufferOverflowEntry
  PrintfBufferOverflowCaller.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld PrintfBufferOverflowCall PrintfBufferOverflowCaller PrintfBufferOverflowEntry SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


Import LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance overflow_staging_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (F : ptr -> iProp Σ) (E : iProp Σ).
Context (Hoverflow : find_fn ge (TAtom "__GI___overflow") = Some (Defined glibc___overflow)).
Context (Hcall : PrintfBufferOverflowCall.printf_overflow_call_spec w0 registry ge F E).

(** Both outcomes preserve the original buffer cells and updated unsigned count.
    EOF clears the printf mode; any other result reaches L88 with the original
    mode and the stream resources returned by the call. *)
Lemma wp_printf_overflow_staging fr bb breg fb ch mode written Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb < 2 ^ 64 -> 0 <= ch < 256 -> 0 <= written < 2 ^ 64 ->
  (F (mkPtr fb (Obj fb)) ⊢ ∃ freg dqf, liveq dqf fb freg ∗
    (liveq dqf fb freg -∗ F (mkPtr fb (Obj fb)))) ->
  live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
  pcell bb 8 (mkPtr (bb + 49) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 written -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 [ch] -∗
  int_cell bb 32 mode -∗ F (mkPtr fb (Obj fb)) -∗ E -∗
  (live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
    pcell bb 8 (mkPtr (bb + 49) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 ((written + 1) mod 2 ^ 64) -∗
    pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 [ch] -∗ int_cell bb 32 0 -∗
    F (mkPtr fb (Obj fb)) -∗ E -∗ Φ RetVoid) -∗
  (∀ e', ⌜lookup (TAtom "v0") e' = Some (WPtr (mkPtr bb (Obj bb)))⌝ -∗
    live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
    pcell bb 8 (mkPtr (bb + 49) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 ((written + 1) mod 2 ^ 64) -∗
    pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 [ch] -∗ int_cell bb 32 mode -∗
    F (mkPtr fb (Obj fb)) -∗ E -∗
    WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e' [] None
      (Enter (TAtom "L88") (Some (TAtom "L74")))) : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfrg Hch Hw Hborrow.
  set (P := (pcell bb 0 (mkPtr (bb + 48) (Obj bb)) ∗
    pcell bb 8 (mkPtr (bb + 49) (Obj bb)) ∗
    pcell bb 16 (mkPtr (bb + 49) (Obj bb)) ∗
    icell bb 24 ((written + 1) mod 2 ^ 64))%I).
  assert (Hframed : PrintfBufferOverflowCall.printf_overflow_call_spec w0 registry ge F (E ∗ P)).
  { intros fr' fp c Ψ Hc Hframe. iIntros "HF (HE & HP) HK".
    iApply (Hcall fr' fp c with "HF HE"); try assumption.
    iNext. iIntros (r Hr) "HF HE".
    iApply ("HK" $! r with "[%] HF [HE HP]"); [done | iFrame]. }
  iIntros "Hb Hbase Hptr Hend Hw Hfp Hch Hm HF HE Hfail Hselect".
  iApply (PrintfBufferOverflowEntry.wp_printf_overflow_entry w0 registry ge fr bb breg written
    with "Hb Hbase Hptr Hend Hw"); try assumption.
  iIntros (e (Hv0 & Hchk)) "Hb Hbase Hptr Hend Hw".
  iApply (PrintfBufferOverflowCaller.wp_printf_overflow_caller w0 registry ge F (E ∗ P) Hoverflow Hframed
    e (Some (TAtom "L62")) bb breg fb ch mode
    with "Hb Hfp Hch Hm HF [HE Hbase Hptr Hend Hw] [Hfail] [Hselect]"); try assumption; try lia.
  - rewrite /P. iFrame.
  - rewrite /P. iIntros "Hb Hfp Hch Hm HF (HE & Hbase & Hptr & Hend & Hw)".
    iApply ("Hfail" with "Hb Hbase Hptr Hend Hw Hfp Hch Hm HF HE").
  - rewrite /P. iIntros (e' Hv0') "Hb Hfp Hch Hm HF (HE & Hbase & Hptr & Hend & Hw)".
    iApply ("Hselect" $! e' with "[%] Hb Hbase Hptr Hend Hw Hfp Hch Hm HF HE"). done.
Qed.

End rules.
