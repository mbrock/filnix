From Glibc Require Import GlibcProgram.
(** The triple for user glibc's `c: __libc_cleanup_pop_restore`
    (SysCode.v, nptl/libc-cleanup.c), the pop that ends the push of
    SysCleanup.v: with `c: cancelhandling` 0 it restores the thread's
    `c: cleanup` and returns without a CAS or `c: __pthread_unwind`. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode FileInv LibioLogic SysWrappers.
From Glibc Require FileInv LibioLogic OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** Integer arithmetic stays folded on an unknown under [cbn]
    (Symbolic.v's decisions): on numbers it computes. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The premises of `c: zthread_self_cookie`'s rule. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** `c: __libc_cleanup_pop_restore(buffer)` after
    [wp_glibc___libc_cleanup_push_defer] of the same buffer, its
    `c: __prev` null and `c: __canceltype` 0: the thread's
    `c: cleanup` is null again, and since the canceltype is deferred
    the call returns at once, [tcb_cleanup_inv] restored. *)
Lemma wp_glibc___libc_cleanup_pop_restore fr bb breg bo Φ :
  call_frame glibc___libc_cleanup_pop_restore [WPtr (mkPtr (bb + bo) (Obj bb))] = Some fr ->
  0 < bb -> 0 <= bo -> (bb + bo) mod 8 = 0 -> bb + bo + 32 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  tcb_pushed (ow_self w0) (mkPtr (bb + bo) (Obj bb)) -∗ live bb breg -∗ pcell bb (bo + 24) null -∗
  int_cell bb (bo + 16) 0 -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ live bb breg -∗ pcell bb (bo + 24) null -∗ int_cell bb (bo + 16) 0 -∗
     Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hbo Hal Hend Hbreg. injection Hfr as <-.
  iIntros "(%tb & %treg & %jb & %Ht & Htl & Hcl & Hjb & Hch) Hbl Hpv [%Hct0 Hct] HK".
  destruct Ht as (Hself & Htb & Htal & Htend & Htreg). step.
  iApply (OsThread.wp_zthread_self_cookie); try self_side; [rewrite Hself; cbn; lia|]. iNext.
  unfold off_cancelhandling in Htend. rewrite Hself. step. step. norm. check "Hbl".
  load_pointer "Hbl Hpv [//]" by ar.
  iNext. iIntros "Hbl Hpv _". check "Htl".
  store_pointer "Htl Hcl" by (ar) preserving wi_store.
  iNext. iIntros "Htl Hcl". step. norm. check "Htl".
  iDestruct "Hch" as "[%Hch0 Hch]".
  load_bytes_dq "Htl Hch" decode (cbn; reflexivity) by ar.
  iNext. iIntros "Htl Hch". step. norm. check "Hbl".
  load_bytes_dq "Hbl Hct" decode (cbn; reflexivity) by ar.
  iNext. iIntros "Hbl Hct". step. closed_ints. branch. step. closed_ints. branch. step.
  iApply wp_ret_void. iNext.
  iApply ("HK" with "[Htl Hcl Hjb Hch] Hbl Hpv [Hct]").
  - iExists tb, treg, jb. iFrame. iPureIntro. unfold off_cancelhandling. repeat split; try reflexivity; lia.
  - iSplit; [iPureIntro; lia|]. iExact "Hct".
  Unshelve. exact breg.
Qed.

End rules.
