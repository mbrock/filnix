(** A partially filled inline buffer remains available after printf publishes
    its current pointer to FILE. Printf resets its base to that pointer,
    without calling the stream or touching the pending character bytes.

    FILE supplies the lifetime for its own interior pointers. The proof
    requires no separate character-allocation lifetime and adds the pending
    span to the count modulo 2^64, including unsigned wraparound. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioPutsInv PrintfBufferFileCode.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsInv OsWorld PrintfBufferFlushInlineRoom SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


From Glibc Require Import PrintfBufferFlushInlineRoom.
Module HLG := LG0.
Import LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Section cases.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance cases_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Lemma case_wrap fr bb breg fb freg oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= 131 -> 0 <= 1 -> 131 + 1 < 133 -> fb + 133 <= r_end freg ->
  fb + 133 <> bb + 176 -> fb + 133 <> bb + 49 ->
  0 <= (2 ^ 64 - 1) < 2 ^ 64 ->
  live bb breg -∗ live fb freg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ pcell fb 40 oldwp -∗
  pcell fb 48 (mkPtr (fb + 133) (Obj fb)) -∗
  pcell bb 0 (mkPtr (fb + 131) (Obj fb)) -∗
  pcell bb 8 (mkPtr (fb + 131 + 1) (Obj fb)) -∗
  pcell bb 16 (mkPtr (fb + 133) (Obj fb)) -∗ icell bb 24 (2 ^ 64 - 1) -∗
  ▷ (live bb breg -∗ live fb freg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (fb + 131 + 1) (Obj fb)) -∗
     pcell fb 48 (mkPtr (fb + 133) (Obj fb)) -∗
     pcell bb 0 (mkPtr (fb + 131 + 1) (Obj fb)) -∗
     pcell bb 8 (mkPtr (fb + 131 + 1) (Obj fb)) -∗
     pcell bb 16 (mkPtr (fb + 133) (Obj fb)) -∗ icell bb 24 0 -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hbo Hused Hspace Hde
    Hstage Hsingle Hw.
  iIntros "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend Hw HK".
  iApply (PrintfBufferFlushInlineRoom.wp_printf_buffer_flush_inline_room w0 registry ge
    fr bb breg fb freg 131 1 133 (2 ^ 64 - 1) oldwp with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend Hw"); try assumption.
  iNext. iIntros "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend Hw".
  change (((2 ^ 64 - 1) + 1) mod 2 ^ 64) with 0 in *.
  iApply ("HK" with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend Hw").
Qed.
Lemma case_control fr bb breg fb freg oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= 131 -> 0 <= 1 -> 131 + 1 < 133 -> fb + 133 <= r_end freg ->
  fb + 133 <> bb + 176 -> fb + 133 <> bb + 49 ->
  0 <= 41 < 2 ^ 64 ->
  live bb breg -∗ live fb freg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ pcell fb 40 oldwp -∗
  pcell fb 48 (mkPtr (fb + 133) (Obj fb)) -∗
  pcell bb 0 (mkPtr (fb + 131) (Obj fb)) -∗
  pcell bb 8 (mkPtr (fb + 131 + 1) (Obj fb)) -∗
  pcell bb 16 (mkPtr (fb + 133) (Obj fb)) -∗ icell bb 24 41 -∗
  ▷ (live bb breg -∗ live fb freg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (fb + 131 + 1) (Obj fb)) -∗
     pcell fb 48 (mkPtr (fb + 133) (Obj fb)) -∗
     pcell bb 0 (mkPtr (fb + 131 + 1) (Obj fb)) -∗
     pcell bb 8 (mkPtr (fb + 131 + 1) (Obj fb)) -∗
     pcell bb 16 (mkPtr (fb + 133) (Obj fb)) -∗ icell bb 24 42 -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hbo Hused Hspace Hde
    Hstage Hsingle Hw.
  iIntros "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend Hw HK".
  iApply (PrintfBufferFlushInlineRoom.wp_printf_buffer_flush_inline_room w0 registry ge
    fr bb breg fb freg 131 1 133 41 oldwp with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend Hw"); try assumption.
  iNext. iIntros "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend Hw".
  change ((41 + 1) mod 2 ^ 64) with 42 in *.
  iApply ("HK" with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend Hw").
Qed.
End cases.
Print Assumptions PrintfBufferFlushInlineRoom.wp_printf_buffer_flush_inline_room.
Print Assumptions case_wrap.
Print Assumptions case_control.
