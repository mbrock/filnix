(** A printf buffer writes directly into a stream buffer when the stream's
    write pointer lies below its end. The switch function borrows these
    pointers and installs them without changing the stream or character bytes.

    Separate lifetime shares allow the character buffer to be the stream's
    inline short buffer. Interior offsets remain explicit, and the rule
    neither acquires a lock nor assumes that a later write will succeed. *)
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

(** Pointer selection leaves the concrete world interpretation unchanged. *)
Local Instance direct_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Pointer loads borrow independent shares of the containing and target allocations. *)


(** Available stream space selects the same allocation and exact interior offsets.
    The borrowed stream pointers and both lifetime shares are returned unchanged. *)
Lemma wp_printf_buffer_switch_direct fr bb breg fb freg db dreg bo eo dqf dqd
    oldbase oldptr oldend Φ :
  call_frame glibc___printf_buffer_to_file_switch [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 48 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= bo -> bo < eo -> db + eo <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  live bb breg -∗ liveq dqf fb freg -∗ liveq dqd db dreg -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗
  pcell fb 40 (mkPtr (db + bo) (Obj db)) -∗ pcell fb 48 (mkPtr (db + eo) (Obj db)) -∗
  pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗
  ▷ (live bb breg -∗ liveq dqf fb freg -∗ liveq dqd db dreg -∗
     pcell bb 40 (mkPtr fb (Obj fb)) -∗
     pcell fb 40 (mkPtr (db + bo) (Obj db)) -∗ pcell fb 48 (mkPtr (db + eo) (Obj db)) -∗
     pcell bb 0 (mkPtr (db + bo) (Obj db)) -∗
     pcell bb 8 (mkPtr (db + bo) (Obj db)) -∗
     pcell bb 16 (mkPtr (db + eo) (Obj db)) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Hbo Hspace Hde Hdr. injection Hfr as <-.
  iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend HK".
  step. step. check "Hb". load_shared "Hb Hfp Hf".
  step. check_shared "Hf". load_shared "Hf Hwp Hd".
  load_shared "Hb Hfp Hf". step. check_shared "Hf".
  load_shared "Hf Hwe Hd". step. step. step. branch_as false. step.
  step. step. load_shared "Hb Hfp Hf". step. check_shared "Hf".
  load_shared "Hf Hwp Hd". check "Hb". store "Hb" "Hptr".
  step. check "Hb". load_shared "Hb Hfp Hf".
  step. check_shared "Hf". load_shared "Hf Hwe Hd".
  check "Hb". store "Hb" "Hend". step. step. step. check "Hb".
  load_shared "Hb Hptr Hd". check "Hb". store "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend").
Qed.

End rules.
