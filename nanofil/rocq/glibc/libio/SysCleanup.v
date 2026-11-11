(** Triples for user glibc's `c: __libc_cleanup_push_defer` and
    `c: __libc_cleanup_pop_restore` (SysCode.v, nptl/libc-cleanup.c)
    over FileInv.v's [tcb_cleanup_inv]: libio's
    `c: _IO_cleanup_region_start_noarg` pushes a cleanup buffer on the
    caller's stack around the walks of the stream list, and pops it
    after.

    The thread's `c: cancelhandling` is 0, so the push stores canceltype
    0 (deferred) and the pop, reading it back, neither CASes the
    cancel type nor reaches `c: __pthread_unwind`: each run is one path
    of loads and stores, taken here step by step. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode FileInv LibioLogic SysWrappers.
Import ListNotations.
Open Scope Z_scope.

(** Integer arithmetic stays folded on an unknown under [cbn]
    (Symbolic.v's decisions): on numbers it computes. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module SysCleanupOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance cleanup_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The premises of `c: zthread_self_cookie`'s rule. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** `c: __libc_cleanup_push_defer(buffer)`, the thread's cleanup
    fields as [tcb_cleanup_inv] says and the buffer's `c: __prev` and
    `c: __canceltype` owned: `c: __prev` is the old `c: cleanup`,
    null, `c: __canceltype` is 0 (deferred, since `c: cancelhandling`
    is 0), and the thread's `c: cleanup` is the buffer. *)
Lemma wp_glibc___libc_cleanup_push_defer fr bb breg bo pv xs Φ :
  call_frame glibc___libc_cleanup_push_defer [WPtr (mkPtr (bb + bo) (Obj bb))] = Some fr ->
  0 < bb -> 0 <= bo -> (bb + bo) mod 8 = 0 -> bb + bo + 32 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  length xs = 4%nat ->
  tcb_cleanup_inv (ow_self w0) -∗ live bb breg -∗ pcell bb (bo + 24) pv -∗ bytes bb (bo + 16) xs -∗
  ▷ (tcb_pushed (ow_self w0) (mkPtr (bb + bo) (Obj bb)) -∗ live bb breg -∗ pcell bb (bo + 24) null -∗
     int_cell bb (bo + 16) 0 -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hbo Hal Hend Hbreg Hxs. injection Hfr as <-.
  iIntros "(%tb & %treg & %jb & %Ht & Htl & Hcl & Hjb & Hch) Hbl Hpv Hct HK".
  destruct Ht as (Hself & Htb & Htal & Htend & Htreg). enter.
  iApply (OTh.wp_zthread_self_cookie w0 registry ge); try self_side; [rewrite Hself; cbn; lia|]. iNext.
  unfold off_cancelhandling in Htend. rewrite Hself. st. st. norm. chk "Htl".
  iApply (wp_raw_load_pointer with "Htl Hcl [//]"); [reflexivity | reflexivity | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Htl Hcl _". chk "Hbl".
  iApply (wp_raw_store_pointer with "Hbl Hpv"); [reflexivity | reflexivity | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Hbl Hpv". st. norm. chk "Htl".
  iDestruct "Hch" as "[%Hch0 Hch]".
  iApply (wp_raw_load_sub_bytes_dq with "Htl Hch"); [reflexivity | reflexivity | reflexivity | cbn; reflexivity |
    left; reflexivity | ar |].
  iNext. iIntros "Htl Hch". st. st. st. closed_ints. br. st. st. st. closed_ints. br. st. st. st. norm.
  chk "Hbl".
  iApply (wp_raw_store_w with "Hbl Hct"); [reflexivity | reflexivity | reflexivity | ar | exact Hxs | wi_store |].
  iNext. iIntros "Hbl Hct". st. norm. chk "Htl".
  iApply (wp_raw_store_pointer with "Htl Hcl"); [reflexivity | reflexivity | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Htl Hcl". iApply wp_ret_void. iNext.
  iApply ("HK" with "[Htl Hcl Hjb Hch] Hbl Hpv [Hct]").
  - iExists tb, treg, jb. iFrame. iPureIntro. unfold off_cancelhandling. repeat split; try reflexivity; lia.
  - iSplit; [iPureIntro; lia|]. iExact "Hct".
  Unshelve. exact treg.
Qed.

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
  destruct Ht as (Hself & Htb & Htal & Htend & Htreg). enter.
  iApply (OTh.wp_zthread_self_cookie w0 registry ge); try self_side; [rewrite Hself; cbn; lia|]. iNext.
  unfold off_cancelhandling in Htend. rewrite Hself. st. st. norm. chk "Hbl".
  iApply (wp_raw_load_pointer with "Hbl Hpv [//]"); [reflexivity | reflexivity | reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hbl Hpv _". chk "Htl".
  iApply (wp_raw_store_pointer with "Htl Hcl"); [reflexivity | reflexivity | reflexivity | ar | ar | wi_store |].
  iNext. iIntros "Htl Hcl". st. norm. chk "Htl".
  iDestruct "Hch" as "[%Hch0 Hch]".
  iApply (wp_raw_load_sub_bytes_dq with "Htl Hch"); [reflexivity | reflexivity | reflexivity | cbn; reflexivity |
    left; reflexivity | ar |].
  iNext. iIntros "Htl Hch". st. norm. chk "Hbl".
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hct"); [reflexivity | reflexivity | reflexivity | cbn; reflexivity |
    left; reflexivity | ar |].
  iNext. iIntros "Hbl Hct". st. closed_ints. br. st. closed_ints. br. st.
  iApply wp_ret_void. iNext.
  iApply ("HK" with "[Htl Hcl Hjb Hch] Hbl Hpv [Hct]").
  - iExists tb, treg, jb. iFrame. iPureIntro. unfold off_cancelhandling. repeat split; try reflexivity; lia.
  - iSplit; [iPureIntro; lia|]. iExact "Hct".
  Unshelve. exact breg.
Qed.

End rules.
End SysCleanupOn.
