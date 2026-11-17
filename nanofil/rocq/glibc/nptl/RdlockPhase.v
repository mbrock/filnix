From Glibc Require Import GlibcProgram.
(** Hello calls gettext after setlocale, and gettext takes setlocale's
    lock for reading. Setlocale leaves that lock in an idle write phase:
    its word has the write-phase bit set, and no thread holds it for
    writing. The rule of [RdlockLogic](RdlockLogic.v) covers only words
    with that bit clear, so this module proves the route that a reader
    takes on a lock left this way.

    The reader adds itself to the count as before. Then it sees the
    write phase and no writer, so it ends the write phase itself with a
    compare-and-swap that clears the bit. Like a writer that hands over
    to readers, it swaps `c: __wrphase_futex` to 0 and wakes waiters only
    if that word had its waiter bit set. In Hello nobody waits, so the
    call returns 0 with the count raised by one reader and the phase
    bit clear. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers RdlockCode RdlockLogic.
From Glibc Require FileInv LibioLogic OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Ltac rw_small x := repeat (rewrite (Z.mod_small x (2 ^ 32)); [|lia]).

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Ltac self_side := first [apply (reg_of registry Hreg); reflexivity
  | apply (ext_fn ge Hext); cbn; tauto | apply (ext_data ge Hext); cbn; tauto].

(** The lowest bit of an odd word is set. *)
Lemma odd_land1 x : x mod 2 = 1 -> Z.land x 1 = 1.
Proof. intros H. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones; [exact H | lia]. Qed.
(** A word that is 1 modulo 4 has its second bit clear. *)
Lemma low1_land2 x : x mod 4 = 1 -> Z.land x 2 = 0.
Proof.
  intros H. change 2 with (Z.land 3 2) at 1. rewrite Z.land_assoc.
  change 3 with (Z.ones 2). rewrite Z.land_ones; [|lia]. change (2 ^ 2) with 4. rewrite H. reflexivity.
Qed.
(** Clearing the lowest bit of an odd word subtracts 1. *)
Lemma odd_lxor1 x : x mod 2 = 1 -> Z.lxor x 1 = x - 1.
Proof.
  intros H. assert (Hx : x = Z.lxor (x - 1) 1).
  { rewrite <- Z.add_nocarry_lxor; [lia|]. change 1 with (Z.ones 1) at 2. rewrite Z.land_ones; [|lia].
    change (2 ^ 1) with 2. Z.div_mod_to_equations; lia. }
  rewrite {1}Hx Z.lxor_assoc Z.lxor_nilpotent Z.lxor_0_r. reflexivity.
Qed.

(** Gettext can read-lock the setlocale lock after setlocale has
    released it. The lock word r then has its write-phase bit set and
    no other flag. The call returns 0 and leaves the word r + 7, which
    counts one more reader and has no write phase. The write-phase
    futex had no waiter bit, and it ends 0. *)
Lemma wp_glibc_rdlock_phase fr lb lreg r wp cw fl tb treg dqt dqi tid Φ :
  call_frame glibc_pthread_rwlock_rdlock [WPtr (mkPtr lb (Obj lb))] = Some fr ->
  ow_self w0 = mkPtr tb (Obj tb) -> 0 < tb -> tb + 724 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  0 < lb -> lb mod 8 = 0 -> lb + 56 <= r_end lreg -> r_end lreg <= 2 ^ 63 ->
  r mod 8 = 1 -> r + 8 < 2 ^ 31 -> (wp = 0 \/ wp = 1) -> cw <> tid ->
  live lb lreg -∗ int_cell lb 0 r -∗ int_cell lb 8 wp -∗ int_cell lb 24 cw -∗ int_cell lb 48 fl -∗
  liveq dqt tb treg -∗ int_cellq dqi tb 720 tid -∗
  ▷ (live lb lreg -∗ int_cell lb 0 (r + 7) -∗ int_cell lb 8 0 -∗ int_cell lb 24 cw -∗ int_cell lb 48 fl -∗
     liveq dqt tb treg -∗ int_cellq dqi tb 720 tid -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hself Htb Htend Htreg Hlb Hlal Hlend Hlreg Hr Hr8 Hwp Hcw. injection Hfr as <-.
  iIntros "Hl [%Hr0 Hrb] [%Hwp0 Hwpb] [%Hcw0 Hcwb] [%Hfl0 Hflb] Htl [%Htid0 Htidb] HK".
  (* No timeout is given, and the thread is not the writer. *)
  repeat step. closed_ints. branch. repeat step. closed_ints. branch. repeat step.
  check "Hl". load_bytes_dq "Hl Hcwb" decode (apply load_sw_int; exact Hcw0) by ar. iNext. iIntros "Hl Hcwb".
  iApply (OsThread.wp_zthread_self_cookie); try self_side; [rewrite Hself; cbn; lia|]. iNext. rewrite Hself.
  repeat step. norm. check_read_dq "Htl" by ar. iNext. iIntros "Htl".
  load_bytes_dq "Htl Htidb" decode (apply load_sw_int; exact Htid0) by ar. iNext. iIntros "Htl Htidb".
  repeat step. rewrite (Z.mod_small cw); [|lia]. rewrite (Z.mod_small tid); [|lia].
  rewrite (proj2 (Z.eqb_neq cw tid) Hcw). closed_ints. branch. repeat step.
  check "Hl". load_bytes_dq "Hl Hflb" decode (apply load_uw_int; exact Hfl0) by ar. iNext. iIntros "Hl Hflb". repeat step.
  (* With writer preference the waiting loop exits at once, because a
     write phase is on. Both values of the flag reach the same add. *)
  assert (Hb1 : Z.land r 1 = 1) by (change 1 with (Z.ones 1) at 1; rewrite Z.land_ones; [|lia]; change (2 ^ 1) with 2; Z.div_mod_to_equations; lia).
  branch_cases; [|repeat step; check "Hl"; load_bytes_dq "Hl Hrb" decode (apply load_uw_int; exact Hr0) by ar; iNext; iIntros "Hl Hrb"; repeat step].
  2: (cbn [edge_label]; rw_small r; change (1 mod 2 ^ 32) with 1; rewrite Hb1; closed_ints; branch; repeat step;
      branch; repeat step).
  2: (branch; repeat step).
  (* Add one reader with a compare-and-swap. *)
  all: repeat step; check "Hl".
  all: load_bytes_dq "Hl Hrb" decode (apply load_uw_int; exact Hr0) by ar.
  all: iNext; iIntros "Hl Hrb"; repeat step; check "Hl".
  all: iApply (wp_raw_cas_w with "Hl Hrb"); [right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | intros _; wi_store |].
  all: iNext; iIntros "Hl Hrb"; rewrite of_bytes_int; [|lia]; rw_small r; rewrite Z.eqb_refl.
  all: repeat step; rewrite ?Z.eqb_refl; closed_ints; branch; repeat step; rw_small (r + 8).
  all: rewrite (proj2 (Z.leb_gt 2147483648 (r + 8)) ltac:(lia)); closed_ints; branch; repeat step.
  (* The write phase is on and nobody holds the lock for writing, so
     this reader ends the write phase. *)
  all: rw_small (r + 8); change (1 mod 2 ^ 32) with 1; rewrite (odd_land1 (r + 8)); [|Z.div_mod_to_equations; lia]; closed_ints; branch; repeat step.
  all: rw_small (r + 8); change (1 mod 2 ^ 32) with 1; rewrite (odd_land1 (r + 8)); [|Z.div_mod_to_equations; lia]; closed_ints; branch; repeat step.
  all: cbn [edge_label]; rw_small (r + 8); change (2 mod 2 ^ 32) with 2; rewrite (low1_land2 (r + 8));
    [|Z.div_mod_to_equations; lia]; closed_ints; branch; repeat step.
  all: rw_small (r + 8); change (1 mod 2 ^ 32) with 1; rewrite (odd_lxor1 (r + 8)); [|Z.div_mod_to_equations; lia].
  all: replace (r + 8 - 1) with (r + 7) by lia.
  all: check "Hl"; iApply (wp_raw_cas_w with "Hl Hrb");
    [right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | intros _; wi_store |].
  all: iNext; iIntros "Hl Hrb".
  all: rewrite (of_bytes_int (r + 8)); [|lia]; rw_small (r + 8); rw_small (r + 7); rewrite Z.eqb_refl.
  all: repeat step; rewrite ?Z.eqb_refl; closed_ints; branch; repeat step; branch; repeat step.
  (* Swap the write-phase futex to 0. It had no waiter bit, so nothing is woken. *)
  all: check "Hl"; load_bytes_dq "Hl Hwpb" decode (apply load_uw_int; exact Hwp0) by ar; iNext; iIntros "Hl Hwpb".
  all: repeat step; check "Hl".
  all: iApply (wp_raw_cas_w with "Hl Hwpb");
      [right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | intros _; wi_store |];
      iNext; iIntros "Hl Hwpb"; rewrite of_bytes_int; [|lia].
  all: rw_small wp; rewrite Z.eqb_refl.
  all: destruct Hwp as [-> | ->]; closed_ints; repeat step; branch; repeat step; branch; repeat step.
  all: iApply wp_ret; [reflexivity | reflexivity |]; iNext; closed_ints.
  all: iApply ("HK" with "Hl [Hrb] [Hwpb] [Hcwb] [Hflb] Htl [Htidb]"); repeat (iSplit; [iPureIntro; lia|]); done.
Qed.

End rules.
