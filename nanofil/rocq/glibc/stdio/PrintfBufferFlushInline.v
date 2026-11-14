From Glibc Require Import GlibcProgram.
(** FILE can hold its character buffer inside its own allocation. Publishing
    a full inline buffer therefore borrows the FILE lifetime for pointer
    reads rather than asking for a second copy of that lifetime.

    Printf then switches to its empty one-character staging area without
    calling the stream. The caller keeps ownership of the character bytes
    because this path changes only pointers and the accumulated count. *)
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

(** Cross-allocation reads borrow the target lifetime without duplicating it. *)


(** An interior pointer borrows its own allocation when read from that allocation. *)


(** Full inline storage switches to staging while preserving the FILE end.
    The count wraps modulo 2^64, and the caller retains all character bytes. *)
Lemma wp_printf_buffer_flush_inline_full fr bb breg fb freg bo used written oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= bo -> 0 <= used -> fb + bo + used <= r_end freg ->
  fb + bo + used <> bb + 176 -> fb + bo + used <> bb + 49 ->
  0 <= written < 2 ^ 64 ->
  live bb breg -∗ live fb freg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ pcell fb 40 oldwp -∗
  pcell fb 48 (mkPtr (fb + bo + used) (Obj fb)) -∗
  pcell bb 0 (mkPtr (fb + bo) (Obj fb)) -∗
  pcell bb 8 (mkPtr (fb + bo + used) (Obj fb)) -∗
  pcell bb 16 (mkPtr (fb + bo + used) (Obj fb)) -∗ icell bb 24 written -∗
  ▷ (live bb breg -∗ live fb freg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (fb + bo + used) (Obj fb)) -∗
     pcell fb 48 (mkPtr (fb + bo + used) (Obj fb)) -∗
     pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 ((written + used) mod 2 ^ 64) -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hbo Hused Hde
    Hstage Hsingle Hw. injection Hfr as <-.
  iIntros "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend Hw HK".
  step. step. check "Hb".
  iApply (wp_raw_load_read_dq with "Hb Hw");
    [reflexivity | vx | left; reflexivity | a2 |].
  iNext. iIntros "Hb Hw".
  step. check "Hb". load_shared "Hb Hptr Hf".
  check "Hb". load_shared "Hb Hbase Hf".
  step. step. step. step. check "Hb". store_long "Hb" "Hw".
  step. load_shared "Hb Hend Hf". step. step. step. step. step. branch_as true. step.
  step. load_shared "Hb Hend Hf". step. step. step. step. step. branch_as true. step.
  step. load_shared "Hb Hend Hf". step. check "Hb". load_shared "Hb Hfp Hf".
  step. check "Hf". load_self_using (wp_raw_load_pointer_self) "Hf Hwe". step. step. step. branch_as false. step.
  step. check "Hb". load_shared "Hb Hfp Hf". step. step. check "Hb".
  load_shared "Hb Hptr Hf". check "Hf". store "Hf" "Hwp".
  check "Hb". load_shared "Hb Hptr Hf". step. check "Hb".
  load_shared "Hb Hend Hf". step. step. step. branch_as false. step.
  step. step. check "Hb". store "Hb" "Hptr".
  step. step. check "Hb". store "Hb" "Hend". step.
  step. step. check "Hb". load_self_using (wp_raw_load_pointer_self) "Hb Hptr". check "Hb". store "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  replace (bb + 48 + 1) with (bb + 49) by lia.
  iApply ("HK" with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend [Hw]").
  replace (fb + bo + used - (fb + bo)) with used by lia.
  iEval (rewrite Z.mod_mod; [|lia]) in "Hw".
  iExact "Hw".
Qed.

End rules.
