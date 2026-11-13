(** After a successful overflow call, printf selects its next buffer and
    returns. It uses available stream space when possible and its own staging
    array otherwise. These rules follow the captured buffer-selection call
    using the existing proofs of that function.

    The caller must own the pointer cells that the switch reads and updates.
    These proofs preserve that ownership. They do not prove that overflow
    returns the required resources. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps PrintfBufferFileCode PrintfBufferStage PrintfBufferDirect.
Import ListNotations.
Open Scope Z_scope.

(** Both calls use the same runtime and OS interpretation as the flush caller. *)
Module PrintfBufferOverflowSwitchOn (R : Runtime) (LG0 : LogicSig R).
Module BS := PrintfBufferStageOn R LG0.
Module BD := PrintfBufferDirectOn R LG0.
Import BS.PI BS.PI.CS BS.PI.CS.SW BS.PI.CS.SW.FI.ML BS.PI.CS.SW.FI.LG
  BS.PI.CS.SW.FI.L BS.PI.CS.SW.OW BS.PI.CS.SW.FI BS.PI.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The switch preserves the surrounding process resources. *)
Local Instance switch_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (Hswitch : find_fn ge (TAtom "__printf_buffer_to_file_switch") =
  Some (Defined glibc___printf_buffer_to_file_switch)).

(** Null stream pointers select printf's staging array without a stream write. *)
Lemma wp_printf_overflow_switch_null e from bb breg fb freg oldbase oldptr oldend Φ :
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  live bb breg -∗ live fb freg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗
  pcell fb 40 null -∗ pcell fb 48 null -∗
  pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗
  ▷ (live bb breg -∗ live fb freg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 null -∗ pcell fb 48 null -∗
     pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Enter (TAtom "L88") from)) : sexpr) {{ Φ }}.
Proof.
  intros Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfr Hv0.
  iIntros "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend HK".
  iApply wp_enter; [reflexivity | destruct from; reflexivity |].
  iNext. cbn [b_insts b_jump].
  iApply wp_call_bind; [vx | exact Hswitch | reflexivity |]. iNext.
  iApply (BS.wp_printf_buffer_switch_null w0 registry ge _ bb breg fb freg
    with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend"); try side.
  iNext. iIntros "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend".
  resume. fs. enter. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend").
Qed.

(** Owned stream storage is selected only when its write pointer precedes
    its end. Fractional lifetime shares also allow FILE-inline storage. *)
Lemma wp_printf_overflow_switch_owned e from bb breg fb freg db dreg bo eo dqf dqd
    oldbase oldptr oldend Φ :
  let start := if bo <? eo then mkPtr (db + bo) (Obj db) else mkPtr (bb + 48) (Obj bb) in
  let stop := if bo <? eo then mkPtr (db + eo) (Obj db) else mkPtr (bb + 176) (Obj bb) in
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= bo -> 0 <= eo -> db + bo <= r_end dreg -> db + eo <= r_end dreg ->
  r_end dreg <= 2 ^ 63 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  live bb breg -∗ liveq dqf fb freg -∗ liveq dqd db dreg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗
  pcell fb 40 (mkPtr (db + bo) (Obj db)) -∗ pcell fb 48 (mkPtr (db + eo) (Obj db)) -∗
  pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗
  ▷ (live bb breg -∗ liveq dqf fb freg -∗ liveq dqd db dreg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (db + bo) (Obj db)) -∗ pcell fb 48 (mkPtr (db + eo) (Obj db)) -∗
     pcell bb 0 start -∗ pcell bb 8 start -∗ pcell bb 16 stop -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Enter (TAtom "L88") from)) : sexpr) {{ Φ }}.
Proof.
  cbn zeta. intros Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfr Hdb Hbo Heo Hdp Hde Hdr Hv0.
  iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend HK".
  iApply wp_enter; [reflexivity | destruct from; reflexivity |].
  iNext. cbn [b_insts b_jump].
  iApply wp_call_bind; [vx | exact Hswitch | reflexivity |]. iNext.
  destruct (Z.ltb_spec bo eo) as [Hspace|Hspace].
  - iApply (BD.wp_printf_buffer_switch_direct w0 registry ge _ bb breg fb freg db dreg bo eo
      with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend"); try side.
    iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend".
    resume. fs. enter. iApply wp_ret_void. iNext.
    iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend").
  - iApply (BS.wp_printf_buffer_switch_staging w0 registry ge _ bb breg fb freg db dreg bo eo
      with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend"); try side.
    iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend".
    resume. fs. enter. iApply wp_ret_void. iNext.
    iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend").
Qed.

End rules.
End PrintfBufferOverflowSwitchOn.
