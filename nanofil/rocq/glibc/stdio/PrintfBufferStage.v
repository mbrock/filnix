(** A printf buffer uses its own staging array when the stream has no write
    buffer or its write pointer has reached the end. These rules follow the
    checked switch function and preserve the stream pointers unchanged.

    The staging array belongs to the same allocation as the printf-buffer
    fields. Selecting it changes three pointer cells, not the array's bytes,
    the accumulated count, stream flags or recursive lock ownership. *)
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

(** The pointer proof uses the existing stream and lifetime rules unchanged. *)
Module PrintfBufferStageOn (R : Runtime) (LG0 : LogicSig R).
Module PI := LibioPutsInvOn R LG0.
Import PI PI.CS PI.CS.SW PI.CS.SW.FI.ML PI.CS.SW.FI.LG PI.CS.SW.FI.L
  PI.CS.SW.OW PI.CS.SW.FI PI.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The switch function shares the caller's concrete world interpretation. *)
Local Instance stage_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A stream with null write pointers selects the full 128-byte staging array.
    The caller keeps the array bytes and every field outside this footprint. *)
Lemma wp_printf_buffer_switch_null fr bb breg fb freg oldbase oldptr oldend Φ :
  call_frame glibc___printf_buffer_to_file_switch [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  live bb breg -∗ live fb freg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗
  pcell fb 40 null -∗ pcell fb 48 null -∗
  pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗
  ▷ (live bb breg -∗ live fb freg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 null -∗ pcell fb 48 null -∗
     pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg. injection Hfr as <-.
  iIntros "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend HK".
  enter. fs. fchk "Hb". fldp "Hb" "Hfp" "Hf".
  fs. fchk "Hf". fldn "Hf" "Hwp". fldp "Hb" "Hfp" "Hf".
  fs. fchk "Hf". fldn "Hf" "Hwe". fs. fs. fs. fbr. fs.
  fs. fs. fchk "Hb". fstp "Hb" "Hptr".
  fs. fs. fchk "Hb". fstp "Hb" "Hend". fs. fs.
  fs. fchk "Hb".
  iApply (wp_raw_load_pointer_self w0 registry ge with "Hb Hptr");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hb Hptr". fchk "Hb". fstp "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  replace (bb + 48 + 128) with (bb + 176) by lia.
  iApply ("HK" with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend").
Qed.

(** Pointer loads preserve separate lifetime shares even when the character
    buffer and stream occupy the same allocation. *)
Local Ltac load_pointer H :=
  iApply (wp_raw_load_pointer_dq with H);
    [reflexivity | vx | left; reflexivity | a2 | a2 | a2 |];
  iNext; iIntros H.

(** A write pointer at or beyond the end also selects the staging array.
    Both original pointers remain owned, including their interior offsets. *)
Lemma wp_printf_buffer_switch_staging fr bb breg fb freg db dreg bo eo dqf dqd
    oldbase oldptr oldend Φ :
  call_frame glibc___printf_buffer_to_file_switch [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= eo -> eo <= bo -> db + bo <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  live bb breg -∗ liveq dqf fb freg -∗ liveq dqd db dreg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗
  pcell fb 40 (mkPtr (db + bo) (Obj db)) -∗ pcell fb 48 (mkPtr (db + eo) (Obj db)) -∗
  pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗
  ▷ (live bb breg -∗ liveq dqf fb freg -∗ liveq dqd db dreg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (db + bo) (Obj db)) -∗ pcell fb 48 (mkPtr (db + eo) (Obj db)) -∗
     pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Heo Hspace Hde Hdr. injection Hfr as <-.
  iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend HK".
  enter. fs. fchk "Hb". load_pointer "Hb Hfp Hf".
  fs. chkq "Hf". load_pointer "Hf Hwp Hd".
  load_pointer "Hb Hfp Hf". fs. chkq "Hf".
  load_pointer "Hf Hwe Hd". fs. fs. fs. fbrv true. fs.
  fs. fs. fchk "Hb". fstp "Hb" "Hptr".
  fs. fs. fchk "Hb". fstp "Hb" "Hend". fs. fs.
  fs. fchk "Hb".
  iApply (wp_raw_load_pointer_self w0 registry ge with "Hb Hptr");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hb Hptr". fchk "Hb". fstp "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  replace (bb + 48 + 128) with (bb + 176) by lia.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend").
Qed.

End rules.
End PrintfBufferStageOn.
