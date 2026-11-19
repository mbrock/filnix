From Glibc Require Import Unit_nptl_pthread_rwlock_unlock_os.
From Glibc Require Import GlibcProgram.
(** After `c: setlocale` changes the global locale, it releases its
    lock with `c: pthread_rwlock_unlock`. The function sees that the
    calling thread is the writer and runs the writer's unlock. This
    module proves that route for the lock that
    [WrlockLogic](WrlockLogic.v) leaves behind.

    Releasing the write lock must leave the lock usable by the next
    caller, which in Hello is gettext taking it for reading. The writer
    first forgets that it owns the lock and empties the futex on which
    other writers would wait. The setlocale lock prefers readers, so no
    waiting writer is handed the lock. With no reader present, the
    function drops the held bit and keeps the write phase on. So the
    lock word goes from 3 to 1, and nothing is woken, because nobody was
    waiting on either futex. *)
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry OsMemLogic OsExternals RdlockLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Import OsExternals Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld OsMemLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Local Ltac self_side := first [apply (reg_of registry Hreg); reflexivity
  | apply (ext_fn ge Hext); cbn; tauto | apply (ext_data ge Hext); cbn; tauto].

(** A thread that holds the setlocale lock for writing can release it
    safely, and the lock ends idle with no writer. The lock must be in
    the state that taking it left, nobody may wait on it, and it must
    prefer readers. *)
Lemma wp_glibc_rwunlock_write fr lb lreg wf sh tb treg dqt dqi tid Φ :
  call_frame Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock [WPtr (mkPtr lb (Obj lb))] = Some fr ->
  ow_self w0 = mkPtr tb (Obj tb) -> 0 < tb -> tb + 724 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  0 < lb -> lb mod 8 = 0 -> lb + 56 <= r_end lreg -> r_end lreg <= 2 ^ 63 ->
  (wf = 0 \/ wf = 1) ->
  live lb lreg -∗ int_cell lb 0 3 -∗ int_cell lb 12 wf -∗ int_cell lb 24 tid -∗ int_cell lb 28 sh -∗
  int_cell lb 48 0 -∗ liveq dqt tb treg -∗ int_cellq dqi tb 720 tid -∗
  ▷ (live lb lreg -∗ int_cell lb 0 1 -∗ int_cell lb 12 0 -∗ int_cell lb 24 0 -∗ int_cell lb 28 sh -∗
     int_cell lb 48 0 -∗ liveq dqt tb treg -∗ int_cellq dqi tb 720 tid -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hself Htb Htend Htreg Hlb Hlal Hlend Hlreg Hwf. injection Hfr as <-.
  iIntros "Hl [%Hr0 Hrb] [%Hwf0 Hwfb] [%Hcw0 Hcwb] [%Hsh0 Hshb] [%Hfl0 Hflb] Htl [%Htid0 Htidb] HK".
  (* The calling thread is the writer. *)
  repeat step. check "Hl". load_bytes_dq "Hl Hcwb" decode (apply load_sw_int; exact Hcw0) by ar.
  iNext. iIntros "Hl Hcwb".
  iApply (OsThread.wp_zthread_self_cookie); try self_side; [rewrite Hself; cbn; lia|]. iNext. rewrite Hself.
  repeat step. norm. check_read_dq "Htl" by ar. iNext. iIntros "Htl".
  load_bytes_dq "Htl Htidb" decode (apply load_sw_int; exact Htid0) by ar. iNext. iIntros "Htl Htidb".
  repeat step. rewrite (Z.mod_small tid); [|lia]. rewrite Z.eqb_refl. closed_ints. branch. repeat step.
  (* The shared flag selects the futex kind; both values are covered. *)
  check "Hl". load_bytes_dq "Hl Hshb" decode (apply load_sw_int; exact Hsh0) by ar. iNext. iIntros "Hl Hshb".
  repeat step. branch_cases; repeat step.
  (* Clear the writer and swap the writers futex to 0. *)
  all: cbn [edge_label]; check "Hl"; store_int "Hl" "Hcwb"; repeat step.
  all: check "Hl"; load_bytes_dq "Hl Hwfb" decode (apply load_uw_int; exact Hwf0) by ar; iNext; iIntros "Hl Hwfb".
  all: repeat step; check "Hl".
  all: iApply (wp_raw_cas_w with "Hl Hwfb");
    [right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | intros _; wi_store |];
    iNext; iIntros "Hl Hwfb"; rewrite of_bytes_int; [|lia].
  all: rw_small wf; rewrite Z.eqb_refl.
  all: destruct Hwf as [-> | ->]; closed_ints; repeat step; branch; repeat step.
  (* The flags prefer readers, so there is no hand-over to a writer. *)
  all: check "Hl"; load_bytes_dq "Hl Hflb" decode (apply load_uw_int; exact Hfl0) by ar; iNext; iIntros "Hl Hflb".
  all: repeat step; closed_ints; branch; repeat step.
  (* Clear the held bit and keep the write phase. *)
  all: check "Hl"; load_bytes_dq "Hl Hrb" decode (apply load_uw_int; exact Hr0) by ar; iNext; iIntros "Hl Hrb".
  all: repeat step; closed_ints; branch; repeat step.
  all: check "Hl"; iApply (wp_raw_cas_w with "Hl Hrb");
    [right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | intros _; wi_store |];
    iNext; iIntros "Hl Hrb"; rewrite of_bytes_int; [|lia]; closed_ints.
  all: lazymatch goal with |- context [if ?c then _ else _] => let c' := eval vm_compute in c in change c with c' end;
    cbn iota.
  (* No reader is present and the old writers futex had no waiter bit, so nothing is woken. *)
  all: repeat step; branch; repeat step; branch; repeat step; branch; repeat step; branch; repeat step.
  all: iApply wp_ret; [reflexivity | reflexivity |]; iNext; closed_ints.
  all: iApply ("HK" with "Hl [Hrb] [Hwfb] [Hcwb] [Hshb] [Hflb] Htl [Htidb]");
    repeat (iSplit; [iPureIntro; lia|]); done.
Qed.

End rules.
