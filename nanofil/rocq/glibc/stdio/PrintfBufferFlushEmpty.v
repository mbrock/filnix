(** A full direct buffer can leave printf using a one-character staging area.
    If no character has entered that area, flushing it does not call the
    stream or inspect its FILE pointer. The accumulated count stays unchanged.

    The caller keeps ownership of the stream and character storage because
    this path accesses neither. The proof follows the checked flush body
    while leaving those resources and the mode in the caller's [[frame]]. *)
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

(** The flush proof uses the existing memory and OS model. *)
Module PrintfBufferFlushEmptyOn (R : Runtime) (LG0 : LogicSig R).
Module PI := LibioPutsInvOn R LG0.
Import PI PI.CS PI.CS.SW PI.CS.SW.FI.ML PI.CS.SW.FI.LG PI.CS.SW.FI.L
  PI.CS.SW.OW PI.CS.SW.FI PI.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Updating the printf count leaves the process's OS resources unchanged. *)
Local Instance empty_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A pointer into the staging array borrows its containing allocation's lifetime. *)
Local Ltac load_self H :=
  iApply (wp_raw_load_pointer_self w0 registry ge with H);
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |];
  iNext; iIntros H.

(** An empty one-character staging area needs only its pointer and count cells.
    Adding its zero pending bytes preserves every canonical 64-bit count. *)
Lemma wp_printf_buffer_flush_empty fr bb breg written Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 <= written < 2 ^ 64 ->
  live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
  pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗ pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗
  icell bb 24 written -∗
  ▷ (live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗ pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗
     icell bb 24 written -∗ Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hwritten. injection Hfr as <-.
  iIntros "Hb Hbase Hptr Hend Hw HK".
  enter. fs. fchk "Hb".
  iApply (wp_raw_load_read_dq with "Hb Hw");
    [reflexivity | vx | left; reflexivity | a2 |].
  iNext. iIntros "Hb Hw".
  fs. fchk "Hb". load_self "Hb Hptr". fchk "Hb". load_self "Hb Hbase".
  fs. fs. fs. fs. fchk "Hb". fstl "Hb" "Hw".
  fs. load_self "Hb Hend". fs. fs. fs. fs. fs. fbrv true. fs.
  fs. load_self "Hb Hend". fs. fs. fs. fs. fs. fbrv false. fs.
  fs. load_self "Hb Hptr". fs. load_self "Hb Hend". fs. fs. fs. fbrv true. fs.
  iApply wp_ret_void. iNext. norm.
  iApply ("HK" with "Hb Hbase Hptr Hend [Hw]").
  iEval (rewrite !Z.sub_diag !Z.add_0_r) in "Hw".
  iExact "Hw".
Qed.

End rules.
End PrintfBufferFlushEmptyOn.
