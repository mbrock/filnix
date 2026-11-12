(** A printf buffer writes directly into a stream buffer when the stream's
    write pointer lies below its end. The switch function borrows these
    pointers and installs them without changing the stream or character bytes.

    Separate lifetime shares allow the character buffer to be the stream's
    inline short buffer. Interior offsets remain explicit, and the rule
    neither acquires a lock nor assumes that a later write will succeed. *)
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

(** The instruction rules preserve the caller's runtime and concrete OS world. *)
Module PrintfBufferDirectOn (R : Runtime) (LG0 : LogicSig R).
Module CS := LibioCloseStepsOn R LG0.
Import CS CS.SW CS.SW.FI.ML CS.SW.FI.LG CS.SW.FI.L CS.SW.OW CS.SW.FI CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Pointer selection leaves the concrete world interpretation unchanged. *)
Local Instance direct_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Pointer loads borrow independent shares of the containing and target allocations. *)
Local Ltac load_pointer H :=
  iApply (wp_raw_load_pointer_dq with H);
    [reflexivity | vx | left; reflexivity | a2 | a2 | a2 |];
  iNext; iIntros H.

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
  enter. fs. fchk "Hb". load_pointer "Hb Hfp Hf".
  fs. chkq "Hf". load_pointer "Hf Hwp Hd".
  load_pointer "Hb Hfp Hf". fs. chkq "Hf".
  load_pointer "Hf Hwe Hd". fs. fs. fs. fbrv false. fs.
  fs. fs. load_pointer "Hb Hfp Hf". fs. chkq "Hf".
  load_pointer "Hf Hwp Hd". fchk "Hb". fstp "Hb" "Hptr".
  fs. fchk "Hb". load_pointer "Hb Hfp Hf".
  fs. chkq "Hf". load_pointer "Hf Hwe Hd".
  fchk "Hb". fstp "Hb" "Hend". fs. fs. fs. fchk "Hb".
  load_pointer "Hb Hptr Hd". fchk "Hb". fstp "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  iApply ("HK" with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend").
Qed.

End rules.
End PrintfBufferDirectOn.
