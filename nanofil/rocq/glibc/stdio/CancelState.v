(** Fatal diagnostics disable cancellation before they lock and write stderr.
    The cancellation flag remains disabled when the diagnostic calls exit.
    This proof follows the actual flag update and saves the previous state
    in caller-owned memory; it does not supply an exit or cleanup contract. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers PrintfStateCode.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The function obtains the current thread's address from the [[runtime]]
    before it reads or changes that thread's cancellation flag. *)
Module CancelStateOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** The concrete OS world provides the registered thread cookie. *)
Local Instance cancel_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The call to obtain the thread address uses the registered runtime function,
    rather than a function body supplied by the linked program. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity
  | apply (ext_fn ge Hext); cbn; tauto | apply (ext_data ge Hext); cbn; tauto].

(** Disabling cancellation from the initial zero state saves zero and installs
    state one. The caller retains the thread object and its saved-state slot. *)
Lemma wp_cancel_disable_save fr tb treg sb sreg so prior Φ :
  call_frame glibc___pthread_setcancelstate
    [WInt 1; WPtr (mkPtr (sb + so) (Obj sb))] = Some fr ->
  ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  0 < sb -> 0 <= so -> sb + so + 4 <= r_end sreg -> r_end sreg <= 2 ^ 63 ->
  live tb treg -∗ int_cell tb 792 0 -∗ live sb sreg -∗ int_cell sb so prior -∗
  ▷ (live tb treg -∗ int_cell tb 792 1 -∗ live sb sreg -∗ int_cell sb so 0 -∗
     Φ (Ret (WInt 0))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hself Htb Htal Htend Htreg Hsb Hso Hsend Hsreg. injection Hfr as <-.
  iIntros "Htl [%Hch Hcb] Hsl [%Hprior Hsave] HK".
  enter. st. closed_ints. br. st. st. st. st. closed_ints. br. st.
  iApply (OTh.wp_zthread_self_cookie w0 registry ge); try self_side;
    [rewrite Hself; cbn; lia|]. iNext. rewrite Hself.
  st. norm. chk "Htl".
  iApply (wp_raw_load_sub_bytes_dq with "Htl Hcb");
    [reflexivity | reflexivity | reflexivity | cbn; reflexivity |
     left; reflexivity | ar |].
  iNext. iIntros "Htl Hcb". st. st. st. closed_ints. br.
  st. st. st. st. st. st. st.
  brv false. st. st. closed_ints. br. st. st. st.
  chk "Hsl".
  iApply (wp_raw_store_w with "Hsl Hsave");
    [reflexivity | reflexivity | reflexivity | ar | reflexivity | wi_store |].
  iNext. iIntros "Hsl Hsave".
  st. st. st. closed_ints. br. st. st. norm. chk "Htl".
  iApply (wp_raw_cas_w with "Htl Hcb");
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |
     ar | ar | intros _; wi_store |].
  iNext. iIntros "Htl Hcb".
  st. closed_ints. br. st. closed_ints. br. st. st. st. closed_ints. br. st.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "Htl [Hcb] Hsl [Hsave]").
  - iSplit; [iPureIntro; lia|iAssumption].
  - iSplit; [iPureIntro; lia|iAssumption].
Qed.

(** A returning diagnostic restores enabled cancellation without writing an
    old-state pointer. The zero flag again excludes asynchronous unwind. *)
Lemma wp_cancel_restore fr tb treg Φ :
  call_frame glibc___pthread_setcancelstate [WInt 0; WPtr null] = Some fr ->
  ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  live tb treg -∗ int_cell tb 792 1 -∗
  ▷ (live tb treg -∗ int_cell tb 792 0 -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hself Htb Htal Htend Htreg. injection Hfr as <-.
  iIntros "Htl [%Hch Hcb] HK".
  enter. st. closed_ints. br. st. st. st. st. closed_ints. br. st.
  iApply (OTh.wp_zthread_self_cookie w0 registry ge); try self_side;
    [rewrite Hself; cbn; lia|]. iNext. rewrite Hself.
  st. norm. chk "Htl".
  iApply (wp_raw_load_sub_bytes_dq with "Htl Hcb");
    [reflexivity | reflexivity | reflexivity | cbn; reflexivity |
     left; reflexivity | ar |].
  iNext. iIntros "Htl Hcb". st. st. st. closed_ints. br.
  st. st. st. st. st. st. st. closed_ints. br.
  st. st. closed_ints. br. st. st. norm. chk "Htl".
  iApply (wp_raw_cas_w with "Htl Hcb");
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |
     ar | ar | intros _; wi_store |].
  iNext. iIntros "Htl Hcb".
  st. closed_ints. br. st. closed_ints. br. st. st. st. closed_ints. br. st.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "Htl [Hcb]"). iSplit; [iPureIntro; lia|iAssumption].
Qed.

End rules.
End CancelStateOn.
