(** Flushing a partially filled direct buffer publishes its current pointer
    to the stream without calling a write function. The stream keeps the
    pending bytes, and printf starts counting again at the current pointer.

    This rule covers separately owned character storage. It preserves that
    storage and does not claim that the pending bytes reach the output. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps PrintfBufferFileCode.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Updating the owned pointer cells preserves the OS resources. *)
Local Instance direct_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Pointer reads borrow the lifetime of the character allocation. *)


(** Available space keeps the direct buffer selected. The count records the
    newly published span modulo 2^64, including unsigned wraparound. *)
Lemma wp_printf_buffer_flush_direct fr bb breg fb freg db dreg bo used eo written dqd oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= bo -> 0 <= used -> bo + used < eo ->
  db + eo <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  db + eo <> bb + 176 -> db + eo <> bb + 49 ->
  0 <= written < 2 ^ 64 ->
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
     pcell bb 16 (mkPtr (db + eo) (Obj db)) -∗ icell bb 24 ((written + used) mod 2 ^ 64) -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Hbo Hused Hspace Hde Hdr
    Hstage Hsingle Hw. injection Hfr as <-.
  iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend Hw HK".
  step. step. check "Hb".
  iApply (wp_raw_load_read_dq with "Hb Hw");
    [reflexivity | vx | left; reflexivity | a2 |].
  iNext. iIntros "Hb Hw".
  step. check "Hb". load_shared "Hb Hptr Hd".
  check "Hb". load_shared "Hb Hbase Hd".
  step. step. step. step. check "Hb". store_long "Hb" "Hw".
  step. load_shared "Hb Hend Hd". step. step. step. step. step. branch_as true. step.
  step. load_shared "Hb Hend Hd". step. step. step. step. step. branch_as true. step.
  step. load_shared "Hb Hend Hd". step. check "Hb". load_shared "Hb Hfp Hf".
  step. check "Hf". load_shared "Hf Hwe Hd". step. step. step. branch_as false. step.
  step. check "Hb". load_shared "Hb Hfp Hf". step. step. check "Hb".
  load_shared "Hb Hptr Hd". check "Hf". store "Hf" "Hwp".
  check "Hb". load_shared "Hb Hptr Hd". step. check "Hb".
  load_shared "Hb Hend Hd". step. step. step. branch_as true. step.
  step. check "Hb". load_shared "Hb Hptr Hd". check "Hb". store "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend [Hw]").
  replace (db + bo + used - (db + bo)) with used by lia.
  iEval (rewrite Z.mod_mod; [|lia]) in "Hw".
  iExact "Hw".
Qed.

End rules.
