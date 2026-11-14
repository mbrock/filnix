(** A full direct buffer publishes its end pointer to FILE before printf
    switches to its one-character staging area. This transition makes no
    stream call and leaves the character bytes with the caller.

    The character storage occupies a separate allocation. The count wraps
    modulo 2^64; publishing bytes does not establish that they reach the output. *)
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

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Pointer updates leave the process's OS resources unchanged. *)
Local Instance full_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Reads borrow the independent lifetime of the pointer's target. *)


(** A full span selects an empty one-character staging area. The FILE end
    and character lifetime survive, and the count includes exactly that span. *)
Lemma wp_printf_buffer_flush_full fr bb breg fb freg db dreg bo used written dqd oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= bo -> 0 <= used ->
  db + bo + used <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  db + bo + used <> bb + 176 -> db + bo + used <> bb + 49 ->
  0 <= written < 2 ^ 64 ->
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
     pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 ((written + used) mod 2 ^ 64) -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Hbo Hused Hde Hdr
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
  load_shared "Hb Hend Hd". step. step. step. branch_as false. step.
  step. step. check "Hb". store "Hb" "Hptr".
  step. step. check "Hb". store "Hb" "Hend". step.
  step. step. check "Hb".
  iApply (wp_raw_load_pointer_self w0 registry ge with "Hb Hptr");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hb Hptr". check "Hb". store "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  replace (bb + 48 + 1) with (bb + 49) by lia.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend [Hw]").
  replace (db + bo + used - (db + bo)) with used by lia.
  iEval (rewrite Z.mod_mod; [|lia]) in "Hw".
  iExact "Hw".
Qed.

End rules.
