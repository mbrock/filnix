From Glibc Require Import Unit_nptl_pthread_rwlock_wrlock_os.
From Glibc Require Import GlibcProgram.
(** glibc's `c: setlocale` takes its global lock for writing before it
    changes the global locale. This module proves the captured
    `c: pthread_rwlock_wrlock` on the route that an idle lock takes.

    The lock word `c: __readers` counts readers above its low three bits,
    which flag a write phase (1), a held write lock (2) and waiting readers
    (4). The function sets the held bit with a compare-and-swap loop. When
    no reader is present and no write phase is on, it then starts a write
    phase with a second compare-and-swap, sets `c: __wrphase_futex` to 1,
    and records the thread's id in `c: __cur_writer`. It always sets
    `c: __writers_futex` to 1.

    The contract covers the two idle words, 0 and 1. In both cases the
    lock ends with the word 3. Starting from 0, the second
    compare-and-swap expects the word that the first one read, which
    lacks the held bit, so it fails once, rereads the word and succeeds
    on the retry. The proof steps through both attempts. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers RdlockLogic.
From Glibc Require FileInv LibioLogic OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Ltac self_side := first [apply (reg_of registry Hreg); reflexivity
  | apply (ext_fn ge Hext); cbn; tauto | apply (ext_data ge Hext); cbn; tauto].

(** On the word 0 the call starts a write phase. Its compare-and-swap
    expects 0 but finds 2, so it fails and rereads the word. The retry
    expects 2, finds it and writes 3. Then the call sets the write-phase
    futex to 1. *)
Local Ltac wr_start_phase :=
  branch; repeat step; branch; repeat step; check "Hl"; iApply (wp_raw_cas_w with "Hl Hrb");
  [right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | intros _; wi_store |];
  iNext; iIntros "Hl Hrb"; rewrite (of_bytes_int (2 mod 2 ^ 32)); [|vm_compute; split; congruence];
  lazymatch goal with |- context [if ?c then _ else _] => let c' := eval vm_compute in c in change c with c' end;
  cbn iota; closed_ints; repeat step; branch; repeat step; branch; repeat step; branch; repeat step; branch;
  repeat step; check "Hl"; iApply (wp_raw_cas_w with "Hl Hrb");
  [right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | intros _; wi_store |];
  iNext; iIntros "Hl Hrb"; rewrite (of_bytes_int (2 mod 2 ^ 32)); [|vm_compute; split; congruence];
  change ((2 mod 2 ^ 32) =? (((2 mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32) with true; cbn iota;
  closed_ints; repeat step; branch; repeat step; branch; repeat step; check "Hl"; store_int "Hl" "Hwpb";
  repeat step.

(** An idle lock with the word r, 0 or 1, ends locked for writing with
    the word 3. The write-phase futex becomes 1 when the call starts the
    write phase, and the thread's id becomes the writer. *)
Lemma wp_glibc_wrlock_idle fr lb lreg r wp wf cw tb treg dqt dqi tid Φ :
  call_frame Unit_nptl_pthread_rwlock_wrlock_os.fn____pthread_rwlock_wrlock [WPtr (mkPtr lb (Obj lb))] = Some fr ->
  ow_self w0 = mkPtr tb (Obj tb) -> 0 < tb -> tb + 724 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  0 < lb -> lb mod 8 = 0 -> lb + 56 <= r_end lreg -> r_end lreg <= 2 ^ 63 ->
  (r = 0 \/ r = 1) -> cw <> tid ->
  live lb lreg -∗ int_cell lb 0 r -∗ int_cell lb 8 wp -∗ int_cell lb 12 wf -∗ int_cell lb 24 cw -∗
  liveq dqt tb treg -∗ int_cellq dqi tb 720 tid -∗
  ▷ (live lb lreg -∗ int_cell lb 0 3 -∗ int_cell lb 8 (if r =? 0 then 1 else wp) -∗ int_cell lb 12 1 -∗
     int_cell lb 24 tid -∗ liveq dqt tb treg -∗ int_cellq dqi tb 720 tid -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hself Htb Htend Htreg Hlb Hlal Hlend Hlreg Hr Hcw. injection Hfr as <-.
  iIntros "Hl [%Hr0 Hrb] [%Hwp0 Hwpb] [%Hwf0 Hwfb] [%Hcw0 Hcwb] Htl [%Htid0 Htidb] HK".
  (* No timeout is given, so the call goes on to the writer test. *)
  repeat step. branch. repeat step. branch. repeat step.
  (* The writer test: the thread does not hold the lock. *)
  check "Hl". load_bytes_dq "Hl Hcwb" decode (apply load_sw_int; exact Hcw0) by ar. iNext. iIntros "Hl Hcwb".
  iApply (OsThread.wp_zthread_self_cookie); try self_side; [rewrite Hself; cbn; lia|]. iNext. rewrite Hself.
  repeat step. norm. check_read_dq "Htl" by ar. iNext. iIntros "Htl".
  load_bytes_dq "Htl Htidb" decode (apply load_sw_int; exact Htid0) by ar. iNext. iIntros "Htl Htidb".
  repeat step. rewrite (Z.mod_small cw); [|lia]. rewrite (Z.mod_small tid); [|lia].
  rewrite (proj2 (Z.eqb_neq cw tid) Hcw). closed_ints. branch. repeat step.
  (* The fetch-or of the held bit, as one compare-and-swap that succeeds. *)
  check "Hl". load_bytes_dq "Hl Hrb" decode (apply load_uw_int; exact Hr0) by ar. iNext. iIntros "Hl Hrb".
  repeat step. check "Hl".
  iApply (wp_raw_cas_w with "Hl Hrb");
    [right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | intros _; wi_store |].
  iNext; iIntros "Hl Hrb"; rewrite of_bytes_int; [|lia]. rw_small r. rewrite Z.eqb_refl. repeat step.
  destruct Hr as [-> | ->]; closed_ints; branch; repeat step; closed_ints; branch; repeat step; branch; repeat step.
  (* Both words set __writers_futex to 1. *)
  all: cbn [edge_label]; check "Hl"; store_int "Hl" "Hwfb"; repeat step; branch; repeat step.
  (* On the word 0 the call starts a write phase, and on the word 1 it
     skips to the end. *)
  1: wr_start_phase.
  (* Both routes record the writer and return 0. *)
  all: cbn [edge_label].
  all: iApply (OsThread.wp_zthread_self_cookie); try self_side; [rewrite Hself; cbn; lia|]; iNext; rewrite Hself.
  all: repeat step; norm.
  all: check_read_dq "Htl" by ar; iNext; iIntros "Htl".
  all: load_bytes_dq "Htl Htidb" decode (apply load_sw_int; exact Htid0) by ar; iNext; iIntros "Htl Htidb".
  all: check "Hl"; store_int "Hl" "Hcwb"; repeat step.
  all: iApply wp_ret; [reflexivity | reflexivity |]; iNext; closed_ints.
  all: rewrite (Z.mod_small tid); [|lia]; cbn [Z.eqb].
  all: iApply ("HK" with "Hl [Hrb] [Hwpb] [Hwfb] [Hcwb] Htl [Htidb]");
    repeat (iSplit; [iPureIntro; lia|]); done.
Qed.

End rules.
