(** Flushing a partially filled direct buffer publishes its current pointer
    to the stream without calling a write function. The stream keeps the
    pending bytes, and printf starts counting again at the current pointer.

    This rule covers separately owned character storage. It preserves that
    storage and does not claim that the pending bytes reach the output. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps PrintfBufferFileCode.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


From Glibc Require Import PrintfBufferFlushDirect.
Module CaseLogic := Logic InterpRuntime.
Module D := PrintfBufferFlushDirectOn InterpRuntime CaseLogic.
Import D.CS D.CS.SW D.CS.SW.FI.ML D.CS.SW.FI.LG D.CS.SW.FI.L
  D.CS.SW.OW D.CS.SW.FI D.CS.SW.ST.
Section cases.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance cases_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Lemma direct_wrap fr bb breg fb freg db dreg dqd oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= 0 -> 0 <= 1 -> 0 + 1 < 2 ->
  db + 2 <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  db + 2 <> bb + 176 -> db + 2 <> bb + 49 ->
  0 <= (2 ^ 64 - 1) < 2 ^ 64 ->
  live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ pcell fb 40 oldwp -∗
  pcell fb 48 (mkPtr (db + 2) (Obj db)) -∗
  pcell bb 0 (mkPtr (db + 0) (Obj db)) -∗
  pcell bb 8 (mkPtr (db + 0 + 1) (Obj db)) -∗
  pcell bb 16 (mkPtr (db + 2) (Obj db)) -∗ icell bb 24 (2 ^ 64 - 1) -∗
  ▷ (live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (db + 0 + 1) (Obj db)) -∗
     pcell fb 48 (mkPtr (db + 2) (Obj db)) -∗
     pcell bb 0 (mkPtr (db + 0 + 1) (Obj db)) -∗
     pcell bb 8 (mkPtr (db + 0 + 1) (Obj db)) -∗
     pcell bb 16 (mkPtr (db + 2) (Obj db)) -∗ icell bb 24 0 -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Hbo Hused Hspace Hde Hdr Hstage Hsingle Hw.
  iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw HK".
  iApply (D.wp_printf_buffer_flush_direct w0 registry ge
    fr bb breg fb freg db dreg 0 1 2 (2 ^ 64 - 1) dqd oldwp
    with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw"); try assumption.
  iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw".
  change (((2 ^ 64 - 1) + 1) mod 2 ^ 64) with 0 in *.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw").
Qed.
Lemma direct_control fr bb breg fb freg db dreg dqd oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= 0 -> 0 <= 1 -> 0 + 1 < 2 ->
  db + 2 <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  db + 2 <> bb + 176 -> db + 2 <> bb + 49 ->
  0 <= 41 < 2 ^ 64 ->
  live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ pcell fb 40 oldwp -∗
  pcell fb 48 (mkPtr (db + 2) (Obj db)) -∗
  pcell bb 0 (mkPtr (db + 0) (Obj db)) -∗
  pcell bb 8 (mkPtr (db + 0 + 1) (Obj db)) -∗
  pcell bb 16 (mkPtr (db + 2) (Obj db)) -∗ icell bb 24 41 -∗
  ▷ (live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (db + 0 + 1) (Obj db)) -∗
     pcell fb 48 (mkPtr (db + 2) (Obj db)) -∗
     pcell bb 0 (mkPtr (db + 0 + 1) (Obj db)) -∗
     pcell bb 8 (mkPtr (db + 0 + 1) (Obj db)) -∗
     pcell bb 16 (mkPtr (db + 2) (Obj db)) -∗ icell bb 24 42 -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Hbo Hused Hspace Hde Hdr Hstage Hsingle Hw.
  iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw HK".
  iApply (D.wp_printf_buffer_flush_direct w0 registry ge
    fr bb breg fb freg db dreg 0 1 2 41 dqd oldwp
    with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw"); try assumption.
  iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw".
  change ((41 + 1) mod 2 ^ 64) with 42 in *.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw").
Qed.
End cases.
Print Assumptions D.wp_printf_buffer_flush_direct.
Print Assumptions direct_wrap.
Print Assumptions direct_control.
