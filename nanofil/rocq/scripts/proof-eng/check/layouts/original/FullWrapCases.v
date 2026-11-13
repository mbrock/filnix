(** A full direct buffer publishes its end pointer to FILE before printf
    switches to its one-character staging area. This transition makes no
    stream call and leaves the character bytes with the caller.

    The character storage occupies a separate allocation. The count wraps
    modulo 2^64; publishing bytes does not establish that they reach the output. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioPutsInv PrintfBufferFileCode.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


From Glibc Require Import PrintfBufferFlushFull.
Module CaseLogic := Logic InterpRuntime.
Module D := PrintfBufferFlushFullOn InterpRuntime CaseLogic.
Import D.PI D.PI.CS D.PI.CS.SW D.PI.CS.SW.FI.ML D.PI.CS.SW.FI.LG D.PI.CS.SW.FI.L
  D.PI.CS.SW.OW D.PI.CS.SW.FI D.PI.CS.SW.ST.
Section cases.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance cases_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Lemma case_wrap fr bb breg fb freg db dreg dqd oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= 0 -> 0 <= 1 ->
  db + 0 + 1 <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  db + 0 + 1 <> bb + 176 -> db + 0 + 1 <> bb + 49 ->
  0 <= (2 ^ 64 - 1) < 2 ^ 64 ->
  live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ pcell fb 40 oldwp -∗
  pcell fb 48 (mkPtr (db + 0 + 1) (Obj db)) -∗
  pcell bb 0 (mkPtr (db + 0) (Obj db)) -∗
  pcell bb 8 (mkPtr (db + 0 + 1) (Obj db)) -∗
  pcell bb 16 (mkPtr (db + 0 + 1) (Obj db)) -∗ icell bb 24 (2 ^ 64 - 1) -∗
  ▷ (live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (db + 0 + 1) (Obj db)) -∗
     pcell fb 48 (mkPtr (db + 0 + 1) (Obj db)) -∗
     pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 0 -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Hbo Hused Hde Hdr
    Hstage Hsingle Hw.
  iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw HK".
  iApply (D.wp_printf_buffer_flush_full w0 registry ge
    fr bb breg fb freg db dreg 0 1 (2 ^ 64 - 1) dqd oldwp with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw"); try assumption.
  iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw".
  change (((2 ^ 64 - 1) + 1) mod 2 ^ 64) with 0 in *.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw").
Qed.
Lemma case_control fr bb breg fb freg db dreg dqd oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= 0 -> 0 <= 1 ->
  db + 0 + 1 <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  db + 0 + 1 <> bb + 176 -> db + 0 + 1 <> bb + 49 ->
  0 <= 41 < 2 ^ 64 ->
  live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ pcell fb 40 oldwp -∗
  pcell fb 48 (mkPtr (db + 0 + 1) (Obj db)) -∗
  pcell bb 0 (mkPtr (db + 0) (Obj db)) -∗
  pcell bb 8 (mkPtr (db + 0 + 1) (Obj db)) -∗
  pcell bb 16 (mkPtr (db + 0 + 1) (Obj db)) -∗ icell bb 24 41 -∗
  ▷ (live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (db + 0 + 1) (Obj db)) -∗
     pcell fb 48 (mkPtr (db + 0 + 1) (Obj db)) -∗
     pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 42 -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Hbo Hused Hde Hdr
    Hstage Hsingle Hw.
  iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw HK".
  iApply (D.wp_printf_buffer_flush_full w0 registry ge
    fr bb breg fb freg db dreg 0 1 41 dqd oldwp with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw"); try assumption.
  iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw".
  change ((41 + 1) mod 2 ^ 64) with 42 in *.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw").
Qed.
End cases.
Print Assumptions D.wp_printf_buffer_flush_full.
Print Assumptions case_wrap.
Print Assumptions case_control.
