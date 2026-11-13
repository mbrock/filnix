(** A partially filled inline buffer remains available after printf publishes
    its current pointer to FILE. Printf resets its base to that pointer,
    without calling the stream or touching the pending character bytes.

    FILE supplies the lifetime for its own interior pointers. The proof
    requires no separate character-allocation lifetime and adds the pending
    span to the count modulo 2^64, including unsigned wraparound. *)
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

(** Publication preserves the existing memory and OS interpretation. *)
Module PrintfBufferFlushInlineRoomOn (R : Runtime) (LG0 : LogicSig R).
Module PI := LibioPutsInvOn R LG0.
Import PI PI.CS PI.CS.SW PI.CS.SW.FI.ML PI.CS.SW.FI.LG PI.CS.SW.FI.L
  PI.CS.SW.OW PI.CS.SW.FI PI.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Updating owned cells leaves the process's OS resources unchanged. *)
Local Instance room_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Reads from printf's header borrow the FILE lifetime for their target. *)
Local Ltac load_pointer H :=
  iApply (wp_raw_load_pointer_dq with H);
    [reflexivity | vx | left; reflexivity | a2 | a2 | a2 |];
  iNext; iIntros H.

(** Remaining inline space keeps the current pointer and end unchanged.
    Publication advances FILE's write pointer and adds the pending span to the count. *)
Lemma wp_printf_buffer_flush_inline_room fr bb breg fb freg bo used eo written oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= bo -> 0 <= used -> bo + used < eo -> fb + eo <= r_end freg ->
  fb + eo <> bb + 176 -> fb + eo <> bb + 49 ->
  0 <= written < 2 ^ 64 ->
  live bb breg -∗ live fb freg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ pcell fb 40 oldwp -∗
  pcell fb 48 (mkPtr (fb + eo) (Obj fb)) -∗
  pcell bb 0 (mkPtr (fb + bo) (Obj fb)) -∗
  pcell bb 8 (mkPtr (fb + bo + used) (Obj fb)) -∗
  pcell bb 16 (mkPtr (fb + eo) (Obj fb)) -∗ icell bb 24 written -∗
  ▷ (live bb breg -∗ live fb freg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (fb + bo + used) (Obj fb)) -∗
     pcell fb 48 (mkPtr (fb + eo) (Obj fb)) -∗
     pcell bb 0 (mkPtr (fb + bo + used) (Obj fb)) -∗
     pcell bb 8 (mkPtr (fb + bo + used) (Obj fb)) -∗
     pcell bb 16 (mkPtr (fb + eo) (Obj fb)) -∗ icell bb 24 ((written + used) mod 2 ^ 64) -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hbo Hused Hspace Hde
    Hstage Hsingle Hw. injection Hfr as <-.
  iIntros "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend Hw HK".
  enter. fs. fchk "Hb".
  iApply (wp_raw_load_read_dq with "Hb Hw");
    [reflexivity | vx | left; reflexivity | a2 |].
  iNext. iIntros "Hb Hw".
  fs. fchk "Hb". load_pointer "Hb Hptr Hf".
  fchk "Hb". load_pointer "Hb Hbase Hf".
  fs. fs. fs. fs. fchk "Hb". fstl "Hb" "Hw".
  fs. load_pointer "Hb Hend Hf". fs. fs. fs. fs. fs. fbrv true. fs.
  fs. load_pointer "Hb Hend Hf". fs. fs. fs. fs. fs. fbrv true. fs.
  fs. load_pointer "Hb Hend Hf". fs. fchk "Hb". load_pointer "Hb Hfp Hf".
  fs. fchk "Hf".
  iApply (wp_raw_load_pointer_self w0 registry ge with "Hf Hwe");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hf Hwe". fs. fs. fs. fbrv false. fs.
  fs. fchk "Hb". load_pointer "Hb Hfp Hf". fs. fs. fchk "Hb".
  load_pointer "Hb Hptr Hf". fchk "Hf". fstp "Hf" "Hwp".
  fchk "Hb". load_pointer "Hb Hptr Hf". fs. fchk "Hb".
  load_pointer "Hb Hend Hf". fs. fs. fs. fbrv true. fs.
  fs. fchk "Hb". load_pointer "Hb Hptr Hf". fchk "Hb". fstp "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  iApply ("HK" with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend [Hw]").
  replace (fb + bo + used - (fb + bo)) with used by lia.
  iEval (rewrite Z.mod_mod; [|lia]) in "Hw".
  iExact "Hw".
Qed.

End rules.
End PrintfBufferFlushInlineRoomOn.
