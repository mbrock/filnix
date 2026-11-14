From Glibc Require Import GlibcProgram.
(** Printf reads its output stream, passes the staged character to overflow,
    and checks the result. EOF marks the printf buffer failed. Any other
    result reaches the checked buffer-selection path.

    This composition keeps two obligations explicit: the overflow contract
    and the ownership needed by buffer selection. It borrows the FILE
    lifetime only for the pointer read and returns it before calling overflow. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode PrintfBufferFileCode PrintfBufferOverflowPrelude
  PrintfBufferOverflowCall PrintfBufferOverflowReturn.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld PrintfBufferOverflowCall PrintfBufferOverflowPrelude PrintfBufferOverflowReturn SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (F : ptr -> iProp Σ)
  (E : iProp Σ).
Context `{Hoverflow : !Defines ge "__GI___overflow" glibc___overflow}.
Context (Hcall : PrintfBufferOverflowCall.printf_overflow_call_spec w0 registry ge F E).

(** The stream lends its lifetime for the pointer read without losing any
    other resources. Neither branch assumes that overflow succeeds. *)
Lemma wp_printf_overflow_caller e from bb breg fb ch mode Φ :
  0 < bb -> bb mod 8 = 0 -> bb + 49 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb < 2 ^ 64 -> 0 <= ch < 256 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb))) ->
  (F (mkPtr fb (Obj fb)) ⊢ ∃ freg dqf, liveq dqf fb freg ∗
    (liveq dqf fb freg -∗ F (mkPtr fb (Obj fb)))) ->
  live bb breg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 [ch] -∗
  int_cell bb 32 mode -∗ F (mkPtr fb (Obj fb)) -∗ E -∗
  (live bb breg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 [ch] -∗
    int_cell bb 32 0 -∗ F (mkPtr fb (Obj fb)) -∗ E -∗ Φ RetVoid) -∗
  (∀ e', ⌜lookup (TAtom "v0") e' = Some (WPtr (mkPtr bb (Obj bb)))⌝ -∗
    live bb breg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 [ch] -∗
    int_cell bb 32 mode -∗ F (mkPtr fb (Obj fb)) -∗ E -∗
    WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e' [] None
      (Enter (TAtom "L88") (Some (TAtom "L74")))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Enter (TAtom "L74") from)) : sexpr) {{ Φ }}.
Proof.
  intros Hbb Hba Hbe Hbr Hfb Hfr Hch Hv0 Hchk Hborrow.
  iIntros "Hb Hfp Hch Hm HF HE Hfail Hselect".
  iDestruct (Hborrow with "HF") as (freg dqf) "[Hf Hclose]".
  iApply (PrintfBufferOverflowPrelude.wp_printf_overflow_prelude e from bb breg fb freg dqf
    with "Hb Hfp Hf"); try close_side.
  iIntros (e' (Hv0' & Hchk' & Hfp')) "Hb Hfp Hf".
  iDestruct ("Hclose" with "Hf") as "HF".
  iApply (PrintfBufferOverflowCall.wp_printf_overflow_call F E Hcall
    e' bb breg (mkPtr fb (Obj fb)) ch with "Hb Hch HF HE"); try close_side.
  iIntros (r e'' (Hr & Hv0'' & Hchk'' & Hret)) "Hb Hch HF HE".
  destruct (Z.eq_dec r 4294967295) as [->|Hneq].
  - iApply (PrintfBufferOverflowReturn.wp_printf_overflow_eof e'' bb breg mode
      with "Hb Hm"); try close_side.
    iNext. iIntros "Hb Hm".
    iApply ("Hfail" with "Hb Hfp Hch Hm HF HE").
  - iApply (PrintfBufferOverflowReturn.wp_printf_overflow_continue e'' r); try assumption.
    iApply ("Hselect" with "[%] Hb Hfp Hch Hm HF HE").
    lookups; reflexivity.
Qed.

End rules.
