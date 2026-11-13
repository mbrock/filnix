(** Printf can hold one character while waiting for room in the stream.
    Flushing that character first updates the count and checks which buffer
    holds it, before calling the stream's overflow routine.

    This rule reaches the overflow block without calling the stream.
    It returns the original pointer cells and the count after unsigned
    wraparound, leaving byte and stream ownership with the caller. *)
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

(** The entry rule preserves the caller's memory and OS interpretation. *)
Module PrintfBufferOverflowEntryOn (R : Runtime) (LG0 : LogicSig R).
Module PI := LibioPutsInvOn R LG0.
Import PI PI.CS PI.CS.SW PI.CS.SW.FI.ML PI.CS.SW.FI.LG PI.CS.SW.FI.L
  PI.CS.SW.OW PI.CS.SW.FI PI.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance overflow_entry_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Staging pointers borrow their containing allocation's lifetime for each read. *)
Local Ltac printf_overflow_entry_load_self H :=
  iApply (wp_raw_load_pointer_self w0 registry ge with H);
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |];
  iNext; iIntros H.

(** The full single-byte area reaches L74 with its checked header address.
    The continuation receives the updated count even when adding one wraps to zero. *)
Lemma wp_printf_overflow_entry fr bb breg written Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 <= written < 2 ^ 64 ->
  live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
  pcell bb 8 (mkPtr (bb + 49) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 written -∗
  (∀ e, ⌜lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) /\
    lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb)))⌝ -∗
    live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
    pcell bb 8 (mkPtr (bb + 49) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 ((written + 1) mod 2 ^ 64) -∗
    WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
      (Enter (TAtom "L74") (Some (TAtom "L62")))) : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hw. injection Hfr as <-.
  iIntros "Hb Hbase Hptr Hend Hw HK".
  enter. fs. fchk "Hb".
  iApply (wp_raw_load_read_dq with "Hb Hw"); [reflexivity | vx | left; reflexivity | a2 |].
  iNext. iIntros "Hb Hw".
  fs. fchk "Hb". printf_overflow_entry_load_self "Hb Hptr".
  fchk "Hb". printf_overflow_entry_load_self "Hb Hbase".
  fs. fs. fs. fs. fchk "Hb". fstl "Hb" "Hw".
  fs. printf_overflow_entry_load_self "Hb Hend". fs. fs. fs. fs. fs. fbrv true. fs.
  fs. printf_overflow_entry_load_self "Hb Hend". fs. fs. fs. fs. fs. fbrv false. fs.
  fs. printf_overflow_entry_load_self "Hb Hptr". fs.
  printf_overflow_entry_load_self "Hb Hend". fs. fs. fs. fbrv false.
  iApply ("HK" $! _ with "[%] Hb Hbase Hptr Hend [Hw]").
  - split; lookups; try reflexivity;
      do 3 f_equal; cbn [ptr_addr ptr_cap]; unwrap2; lia.
  - norm. replace (bb + 49 - (bb + 48)) with 1 by lia.
    iEval (rewrite Z.mod_mod; [|lia]) in "Hw". iExact "Hw".
Qed.

End rules.
End PrintfBufferOverflowEntryOn.
