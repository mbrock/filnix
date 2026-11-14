From Glibc Require Import GlibcProgram.
(** A full direct buffer can leave printf using a one-character staging area.
    If no character has entered that area, flushing it does not call the
    stream or inspect its FILE pointer. The accumulated count stays unchanged.

    The caller keeps ownership of the stream and character storage because
    this path accesses neither. The proof follows the checked flush body
    while leaving those resources and the mode in the caller's [[frame]]. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioPutsInv PrintfBufferFileCode.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsInv OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A pointer into the staging array borrows its containing allocation's lifetime. *)


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
  step. step. check "Hb".
  iApply (wp_raw_load_read_dq with "Hb Hw");
    [reflexivity | vx | left; reflexivity | a2 |].
  iNext. iIntros "Hb Hw".
  step. check "Hb". load_self_using (wp_raw_load_pointer_self) "Hb Hptr". check "Hb". load_self_using (wp_raw_load_pointer_self) "Hb Hbase".
  step. step. step. step. check "Hb". store_long "Hb" "Hw".
  step. load_self_using (wp_raw_load_pointer_self) "Hb Hend". step. step. step. step. step. branch_as true. step.
  step. load_self_using (wp_raw_load_pointer_self) "Hb Hend". step. step. step. step. step. branch_as false. step.
  step. load_self_using (wp_raw_load_pointer_self) "Hb Hptr". step. load_self_using (wp_raw_load_pointer_self) "Hb Hend". step. step. step. branch_as true. step.
  iApply wp_ret_void. iNext. norm.
  iApply ("HK" with "Hb Hbase Hptr Hend [Hw]").
  iEval (rewrite !Z.sub_diag !Z.add_0_r) in "Hw".
  iExact "Hw".
Qed.

End rules.
