(** A printf buffer remembers output failure by setting its mode to zero.
    Completion then returns minus one without reading the buffer pointers
    or the accumulated character count. This rule preserves that failure
    path instead of assuming that earlier output succeeded.

    The rule follows the actual checked body of glibc's completion function.
    It does not yet cover a live buffer's count or overflow paths. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers PrintfStateCode.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The proof shares the existing [[runtime]], heap ownership and OS interpretation. *)
Module PrintfBufferDoneOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The completion body runs in the same concrete world as its caller. *)
Local Instance done_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A failed buffer needs only its live mode field. Its other fields and errno
    remain outside the footprint and can stay in the caller's frame. *)
Lemma wp_printf_buffer_done_failed fr bb breg Φ :
  call_frame glibc___printf_buffer_done [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  live bb breg -∗ int_cell bb 32 0 -∗
  ▷ (live bb breg -∗ int_cell bb 32 0 -∗ Φ (Ret (WInt 4294967295))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hal Hend Hreg. injection Hfr as <-.
  iIntros "Hl [%Hm Hmode] HK". enter. st. norm. chk "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hmode");
    [reflexivity | reflexivity | reflexivity | cbn; reflexivity |
     left; reflexivity | ar |].
  iNext. iIntros "Hl Hmode". st. closed_ints. br. st.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "Hl [Hmode]"). iSplit; [iPureIntro; lia|iExact "Hmode"].
Qed.

End rules.
End PrintfBufferDoneOn.
