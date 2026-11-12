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

(** Publication uses the existing memory and OS interpretation. *)
Module PrintfBufferFlushDirectOn (R : Runtime) (LG0 : LogicSig R).
Module CS := LibioCloseStepsOn R LG0.
Import CS CS.SW CS.SW.FI.ML CS.SW.FI.LG CS.SW.FI.L CS.SW.OW CS.SW.FI CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Updating the owned pointer cells preserves the OS resources. *)
Local Instance direct_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Pointer reads borrow the lifetime of the character allocation. *)
Local Ltac load_pointer H :=
  iApply (wp_raw_load_pointer_dq with H);
    [reflexivity | vx | left; reflexivity | a2 | a2 | a2 |];
  iNext; iIntros H.

(** Available space keeps the direct buffer selected. The count records the
    newly published span, with an explicit bound excluding integer wrap. *)
Lemma wp_printf_buffer_flush_direct fr bb breg fb freg db dreg bo used eo written dqd oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= bo -> 0 <= used -> bo + used < eo ->
  db + eo <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  db + eo <> bb + 176 -> db + eo <> bb + 49 ->
  0 <= written -> written + used < 2 ^ 64 ->
  live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ pcell fb 40 oldwp -∗
  pcell fb 48 (mkPtr (db + eo) (Obj db)) -∗
  pcell bb 0 (mkPtr (db + bo) (Obj db)) -∗
  pcell bb 8 (mkPtr (db + bo + used) (Obj db)) -∗
  pcell bb 16 (mkPtr (db + eo) (Obj db)) -∗ icell bb 24 written -∗
  ▷ (live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (db + bo + used) (Obj db)) -∗
     pcell fb 48 (mkPtr (db + eo) (Obj db)) -∗
     pcell bb 0 (mkPtr (db + bo + used) (Obj db)) -∗
     pcell bb 8 (mkPtr (db + bo + used) (Obj db)) -∗
     pcell bb 16 (mkPtr (db + eo) (Obj db)) -∗ icell bb 24 (written + used) -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Hbo Hused Hspace Hde Hdr
    Hstage Hsingle Hw Htotal. injection Hfr as <-.
  iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw HK".
  enter. fs. fchk "Hb".
  iApply (wp_raw_load_read_dq with "Hb Hw");
    [reflexivity | vx | left; reflexivity | a2 |].
  iNext. iIntros "Hb Hw".
  fs. fchk "Hb". load_pointer "Hb Hptr Hd".
  fchk "Hb". load_pointer "Hb Hbase Hd".
  fs. fs. fs. fs. fchk "Hb". fstl "Hb" "Hw".
  fs. load_pointer "Hb Hend Hd". fs. fs. fs. fs. fs. fbrv true. fs.
  fs. load_pointer "Hb Hend Hd". fs. fs. fs. fs. fs. fbrv true. fs.
  fs. load_pointer "Hb Hend Hd". fs. fchk "Hb". load_pointer "Hb Hfp Hf".
  fs. fchk "Hf". load_pointer "Hf Hwe Hd". fs. fs. fs. fbrv false. fs.
  fs. fchk "Hb". load_pointer "Hb Hfp Hf". fs. fs. fchk "Hb".
  load_pointer "Hb Hptr Hd". fchk "Hf". fstp "Hf" "Hwp".
  fchk "Hb". load_pointer "Hb Hptr Hd". fs. fchk "Hb".
  load_pointer "Hb Hend Hd". fs. fs. fs. fbrv true. fs.
  fs. fchk "Hb". load_pointer "Hb Hptr Hd". fchk "Hb". fstp "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend [Hw]").
  replace (db + bo + used - (db + bo)) with used by lia.
  iExact "Hw".
Qed.

End rules.
End PrintfBufferFlushDirectOn.
