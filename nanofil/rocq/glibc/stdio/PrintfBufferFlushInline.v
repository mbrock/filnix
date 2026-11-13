(** FILE can hold its character buffer inside its own allocation. Publishing
    a full inline buffer therefore borrows the FILE lifetime for pointer
    reads rather than asking for a second copy of that lifetime.

    Printf then switches to its empty one-character staging area without
    calling the stream. The caller keeps ownership of the character bytes
    because this path changes only pointers and the accumulated count. *)
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

(** The inline transition uses the same OS interpretation as its caller. *)
Module PrintfBufferFlushInlineOn (R : Runtime) (LG0 : LogicSig R).
Module PI := LibioPutsInvOn R LG0.
Import PI PI.CS PI.CS.SW PI.CS.SW.FI.ML PI.CS.SW.FI.LG PI.CS.SW.FI.L
  PI.CS.SW.OW PI.CS.SW.FI PI.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Updating owned cells preserves the process's OS resources. *)
Local Instance inline_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Cross-allocation reads borrow the target lifetime without duplicating it. *)
Local Ltac load_pointer H :=
  iApply (wp_raw_load_pointer_dq with H);
    [reflexivity | vx | left; reflexivity | a2 | a2 | a2 |];
  iNext; iIntros H.

(** An interior pointer borrows its own allocation when read from that allocation. *)
Local Ltac load_self H :=
  iApply (wp_raw_load_pointer_self w0 registry ge with H);
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |];
  iNext; iIntros H.

(** Full inline storage switches to staging while preserving the FILE end.
    The count bound excludes wrap, and the caller retains all character bytes. *)
Lemma wp_printf_buffer_flush_inline_full fr bb breg fb freg bo used written oldwp Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= bo -> 0 <= used -> fb + bo + used <= r_end freg ->
  fb + bo + used <> bb + 176 -> fb + bo + used <> bb + 49 ->
  0 <= written -> written + used < 2 ^ 64 ->
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
     pcell bb 16 (mkPtr (bb + 49) (Obj bb)) -∗ icell bb 24 (written + used) -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hbo Hused Hde
    Hstage Hsingle Hw Htotal. injection Hfr as <-.
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
  fs. fchk "Hf". load_self "Hf Hwe". fs. fs. fs. fbrv false. fs.
  fs. fchk "Hb". load_pointer "Hb Hfp Hf". fs. fs. fchk "Hb".
  load_pointer "Hb Hptr Hf". fchk "Hf". fstp "Hf" "Hwp".
  fchk "Hb". load_pointer "Hb Hptr Hf". fs. fchk "Hb".
  load_pointer "Hb Hend Hf". fs. fs. fs. fbrv false. fs.
  fs. fs. fchk "Hb". fstp "Hb" "Hptr".
  fs. fs. fchk "Hb". fstp "Hb" "Hend". fs.
  fs. fs. fchk "Hb". load_self "Hb Hptr". fchk "Hb". fstp "Hb" "Hbase".
  iApply wp_ret_void. iNext. norm.
  replace (bb + 48 + 1) with (bb + 49) by lia.
  iApply ("HK" with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend [Hw]").
  replace (fb + bo + used - (fb + bo)) with used by lia.
  iExact "Hw".
Qed.

End rules.
End PrintfBufferFlushInlineOn.
