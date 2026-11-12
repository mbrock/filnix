(** A stream can ask glibc to write without changing thread cancellation
    state. Both write branches must preserve the same bytes and stream
    fields before the loop can continue. This file proves that they do,
    following the actual join block rather than assuming a call rule. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic
  SysWrappers LibioWriteExit LibioWriteCallDq.
Import ListNotations.
Open Scope Z_scope.

(** The call branches join at this block before testing the result. *)
Definition fw_L16 : block := Eval vm_compute in
  match find_block (TAtom "L16") (fn_blocks glibc__IO_new_file_write) with
  | Some b => b | None => mkBlock (TAtom "L16") [] [] JRetVoid end.

(** The rules use the caller's [[runtime]] and program logic. *)
Module LibioWriteJoinDqOn (R : Runtime) (LG0 : LogicSig R).
Module WC := LibioWriteCallDqOn R LG0.
Import WC WC.WE WC.WE.SW WC.WE.SW.FI.ML WC.WE.SW.FI.LG WC.WE.SW.FI.L
  WC.WE.SW.OW WC.WE.SW.FI WC.WE.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write)).

(** Both branches use the same OS interpretation. *)
Local Instance write_join_dq_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The loop receives its write result in the same variable after either
    branch. When the stream requests noncanceling writes, the environment
    must provide the captured noncanceling wrapper. Otherwise only the
    ordinary wrapper is needed. *)
Lemma wp_file_write_join_dq fb freg f2 fd dq b reg c o xs eb t e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (Z.land f2 2 = 0 \/
    Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> c = Obj b \/ c = Ro b ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 < t <= Z.of_nat (length xs) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "pr.2") e = Some (WInt t) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b + o + (Z.of_nat (length xs) - t)) c)) ->
  live fb freg -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗ liveq dq b reg -∗
  bytesq dq b o xs -∗ errno_any eb -∗
  ▷ (∀ e' k, ⌜(forall x, x = TAtom "v0" \/ x = TAtom "v4" \/ x = TAtom "pr.1" \/ x = TAtom "pr.2" ->
                lookup x e' = lookup x e) /\
              lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (fb + off_flags2) (Obj fb))) /\
              lookup (TAtom "v37") e' = Some (WInt k) /\
              ((0 <= k <= t /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1)⌝ -∗
     live fb freg -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗ liveq dq b reg -∗
     bytesq dq b o xs -∗ errno_any eb -∗
     WP (ERun (mkFrame glibc__IO_new_file_write e' [] None
       (Exec (TAtom "L16") (b_insts fw_L16) (b_jump fw_L16))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_new_file_write e [] None
    (Enter (TAtom "L9") (Some (TAtom "L8")))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hcalls Hf2r Hfd He Hc Hb Ho Hbend Hreg' Hy Ht Hv0 Ht' Hp.
  iIntros "Hl Hfl2 Hfd Hbl Hxs Herr HK".
  destruct Hcalls as [Hf2 | [Hf2 Hnocancel]].
  - iApply (wp_file_write_call_dq w0 registry ge Hreg Hext Hwrite
      fb freg f2 fd dq b reg c o xs eb t with "Hl Hfl2 Hfd Hbl Hxs Herr"); try assumption.
    iNext. iIntros (e' k (Hsame & Hchk & Hresult & Hk)) "Hl Hfl2 Hfd Hbl Hxs Herr".
    assert (Hk64 : 0 <= k < 2 ^ 64) by (unfold file_size in Hend; lia).
    st. st.
    iApply ("HK" $! _ k with "[%] Hl Hfl2 Hfd Hbl Hxs Herr").
    split_and!.
    + intros x Hx. pose proof (Hsame x Hx) as Hlookup.
      destruct Hx as [-> | [-> | [-> | ->]]]; lookups; rewrite Hlookup; lookups; reflexivity.
    + lookups. reflexivity.
    + lookups. rewrite Z.mod_small; [reflexivity | exact Hk64].
    + exact Hk.
  - iApply (wp_file_write_call_nocancel_dq w0 registry ge Hreg Hext Hnocancel
      fb freg f2 fd dq b reg c o xs eb t with "Hl Hfl2 Hfd Hbl Hxs Herr"); try assumption.
    iNext. iIntros (e' k (Hsame & Hchk & Hresult & Hk)) "Hl Hfl2 Hfd Hbl Hxs Herr".
    assert (Hk64 : 0 <= k < 2 ^ 64) by (unfold file_size in Hend; lia).
    st. st.
    iApply ("HK" $! _ k with "[%] Hl Hfl2 Hfd Hbl Hxs Herr").
    split_and!.
    + intros x Hx. pose proof (Hsame x Hx) as Hlookup.
      destruct Hx as [-> | [-> | [-> | ->]]]; lookups; rewrite Hlookup; lookups; reflexivity.
    + lookups. reflexivity.
    + lookups. rewrite Z.mod_small; [reflexivity | exact Hk64].
    + exact Hk.
Qed.

End rules.
End LibioWriteJoinDqOn.
