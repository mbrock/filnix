(** A full direct buffer publishes its end pointer to FILE before printf
    switches to its one-character staging area. This transition makes no
    stream call and leaves the character bytes with the caller.

    The rule uses separately owned character storage and a count bound
    excluding wrap. It does not establish that any bytes reach the output. *)
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

(** The transition preserves the existing OS interpretation. *)
Module PrintfBufferFlushFullOn (R : Runtime) (LG0 : LogicSig R).
Module PI := LibioPutsInvOn R LG0.
Import PI PI.CS PI.CS.SW PI.CS.SW.FI.ML PI.CS.SW.FI.LG PI.CS.SW.FI.L
  PI.CS.SW.OW PI.CS.SW.FI PI.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Pointer updates leave the process's OS resources unchanged. *)
Local Instance full_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Reads borrow the independent lifetime of the pointer's target. *)
Local Ltac load_pointer H :=
  iApply (wp_raw_load_pointer_dq with H);
    [reflexivity | vx | left; reflexivity | a2 | a2 | a2 |];
  iNext; iIntros H.

(** A full span selects an empty one-character staging area. The FILE end
    and character lifetime survive, and the count includes exactly that span. *)
Lemma wp_printf_buffer_flush_full fr bb breg fb freg db dreg bo used written dqd oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= bo -> 0 <= used ->
  db + bo + used <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  db + bo + used <> bb + 176 -> db + bo + used <> bb + 49 ->
  0 <= written -> written + used < 2 ^ 64 ->
  live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ pcell fb 40 oldwp -∗
  pcell fb 48 (mkPtr (db + bo + used) (Obj db)) -∗
  pcell bb 0 (mkPtr (db + bo) (Obj db)) -∗
  pcell bb 8 (mkPtr (db + bo + used) (Obj db)) -∗
  pcell bb 16 (mkPtr (db + bo + used) (Obj db)) -∗ icell bb 24 written -∗
  ▷ (live bb breg -∗ live fb freg -∗ liveq dqd db dreg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (db + bo + used) (Obj db)) -∗
     pcell fb 48 (mkPtr (db + bo + used) (Obj db)) -∗
     pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 (written + used) -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Hbo Hused Hde Hdr
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
  load_pointer "Hb Hend Hd". fs. fs. fs. fbrv false. fs.
  fs. fs. fchk "Hb". fstp "Hb" "Hptr".
  fs. fs. fchk "Hb". fstp "Hb" "Hend". fs.
  fs. fs. fchk "Hb".
  iApply (wp_raw_load_pointer_self w0 registry ge with "Hb Hptr");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hb Hptr". fchk "Hb". fstp "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  replace (bb + 48 + 1) with (bb + 49) by lia.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend [Hw]").
  replace (db + bo + used - (db + bo)) with used by lia.
  iExact "Hw".
Qed.

End rules.
End PrintfBufferFlushFullOn.
