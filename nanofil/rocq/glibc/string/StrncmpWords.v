(** Once `c: strncmp` aligns the first string pointer to an 8-byte
    boundary, it compares 64-bit words while counting down the remaining
    byte limit r. If the second pointer is also aligned, [aligned_loop]
    loads one word from each string per iteration; otherwise,
    [unaligned_loop] shifts and combines consecutive words from the
    second string with [merge].

    Because `c: strncmp` must never compare past the byte limit r, each
    iteration exits to the final comparison epilogues when r drops to
    eight or fewer bytes, or when the current word pair differs. When
    two equal words contain a zero byte and more than eight bytes
    remain, the loop returns zero immediately via [word_zero_n]. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrncmpCode StrcmpBits StrcmpLoop
  StrncmpBits StrncmpLoop.
From Glibc Require StrcmpLoop StrncmpLoop WordString.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.


(** Module [SN] provides the final comparison epilogue lemmas for
    `c: strncmp`. *)
(** Module [SL] provides the shared stepping and window-read lemmas. *)
(** Module [WS] provides the word-window string representation. *)
(** Module [LG] re-exports the program logic instance LG0. *)
Module LG := LG0.
(** Module [L] provides the nanofil language definition for LG. *)
Module L := LG.L.
Import L LG WordString StrcmpLoop.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** Instance [rules_irisGS] builds the [[iris]] machine semantics from
    the external registry and world invariant. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** Notation [gexpr] abbreviates expressions in the instantiated language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Tactic [sl] steps past a `let` instruction while keeping its bound
    value symbolic. *)

(** Tactic [sv] steps past a `let` instruction after resolving its
    operand variables from the environment. *)

(** Tactic [sf] steps past a capability `flight` check instruction. *)

(** Tactic [en] enters the target basic block of a pending frame jump. *)

(** Tactic [sg] steps through a `goto` terminator and immediately enters
    its destination block. *)

(** Tactic [sb] steps past a conditional `branch` instruction without
    evaluating its condition. *)

(** Tactic [norm] rewrites the integer held by variable name to v using
    tactic tac. *)
Ltac norm name v tac :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by tac end.
(** Tactic [normt] normalizes the integer in the newest local variable
    to v using tactic tac. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Tactic [normp] rewrites the address of the pointer held by variable
    name to v using linear arithmetic. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.
(** To avoid repeating boilerplate at the start of each loop proof,
    tactic [facts] extracts the address bounds and byte-agreement
    hypotheses from both strings. *)
Ltac facts Hs1 Hs2 :=
  destruct (shape_facts _ _ _ _ _ Hs1) as (B1 & S1 & M1 & P1 & K1 & E1 & R1 & N1 & C1);
  destruct (shape_facts _ _ _ _ _ Hs2) as (B2 & S2 & M2 & P2 & K2 & E2 & R2 & N2 & C2);
  pose proof (ss_words _ _ _ _ _ Hs1) as F1; pose proof (ss_words _ _ _ _ _ Hs2) as F2;
  pose proof (ss_chars _ _ _ _ _ Hs1) as H1; pose proof (sbyte_agree _ _ _ _ _ Hs1) as A1;
  pose proof (sbyte_agree _ _ _ _ _ Hs2) as A2.

(** Constant [blk12] holds the header block of the aligned word loop in
    `__GI_strncmp`. *)
Definition blk12 : block := Eval vm_compute in StrncmpLoop.nblk "iw_1.L12".

(** Lemma [aligned_loop] proves by induction on the remaining words of
    the first string that comparing aligned 64-bit words up to r bytes
    returns [strncmp_res] (c + r) and restores both windows. *)
Lemma aligned_loop dq1 dq2 p1 p2 b1 b2 reg1 reg2 ws1 ws2 s1 s2 c r Q1 Q2 e Φ :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 -> 0 <= c -> 0 < r < 2 ^ 64 ->
  ptr_addr p1 mod 8 + c = 8 * Q1 -> ptr_addr p2 mod 8 + c = 8 * Q2 -> same_upto (sbyte p1 ws1) (sbyte p2 ws2) c ->
  wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
  (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
   Φ (Ret (WInt (strncmp_res (c + r) s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strncmp (put (TAtom "iw_1.pr.1") (WPtr (mkPtr (ptr_addr p1 + c + 8) (ptr_cap p1)))
       (put (TAtom "iw_1.pr.2") (WPtr (mkPtr (ptr_addr p2 + c + 8) (ptr_cap p2)))
       (put (TAtom "iw_1.pr.3") (WInt (wrd ws1 Q1)) (put (TAtom "iw_1.pr.4") (WInt r)
       (put (TAtom "iw_1.pr.5") (WInt (wrd ws2 Q2)) e))))) [] None
       (Exec (TAtom "iw_1.L12") (b_insts blk12) (b_jump blk12))) : gexpr) {{ Φ }}.
Proof.
  intros Hs1 Hs2. facts Hs1 Hs2.
  remember (Z.to_nat (Z.of_nat (List.length ws1) - Q1)) as n eqn:Hn.
  revert c r Q1 Q2 e Hn. induction n as [|n IH]; intros c r Q1 Q2 e Hn Hc [Hr0 Hr] HQ1 HQ2 Hsame;
    destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame) as [L1 L2]; [exfalso; lia|].
  iIntros "W1 W2 HK". cbn [blk12 b_insts b_jump].
  pose proof (wrd_range ws1 Q1 F1) as X1. pose proof (wrd_range ws2 Q2 F2) as X2.
  assert (Hb : forall u, 0 <= u < 8 -> sbyte p1 ws1 (c + u) = byte_of (wrd ws1 Q1) u /\
                                     sbyte p2 ws2 (c + u) = byte_of (wrd ws2 Q2) u)
    by (intros u Hu; unfold sbyte; split; apply bt_at; lia).
  step_symbolic. branch_symbolic. rewrite (Z.mod_small (wrd ws1 Q1)); [|lia]. rewrite (Z.mod_small (wrd ws2 Q2)); [|lia].
  destruct (Z.eqb_spec (wrd ws1 Q1) (wrd ws2 Q2)) as [Exy|Nxy]; close_if.
  - step. step_symbolic. branch_symbolic. rewrite (Z.mod_small r); [|lia]. change (8 mod 2 ^ 64) with 8.
    destruct (Z.leb_spec r 8) as [Hr8|Hr8]; close_if.
    + eapply (StrncmpLoop.fin_a registry wi ge _ _ _ s1 s2 _ _ c (wrd ws1 Q1) (wrd ws2 Q2) 8 r);
        [reflexivity | reflexivity | reflexivity | lia | lia | lia | exact H1 | exact A1 | exact A2 | |].
      { split; [lia|]. split; [exact Hsame|]. split; [lia|]. split; [lia|]. split; [exact Hb | left; lia]. }
      iApply ("HK" with "W1 W2").
    + step. step_symbolic. normt (r - 8) ltac:(arith). do 4 step_symbolic. normt (loop_mask (wrd ws1 Q1)) ltac:(reflexivity). step_symbolic. branch_symbolic.
      rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _)).
      destruct (Z.eq_dec (loop_mask (wrd ws1 Q1)) 0) as [Hz|Hz].
      * rewrite Hz. close_if. step.
        assert (Hsame' : same_upto (sbyte p1 ws1) (sbyte p2 ws2) (c + 8)).
        { apply (word_same _ _ c (wrd ws1 Q1) (wrd ws2 Q2) Hc Hsame Hb). intros u Hu. rewrite -Exy. split; [done|].
          apply (loop_mask_zero _ X1); [exact Hz | exact Hu]. }
        destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame') as [L1' L2'].
        step. normp "iw_1.v34" (ptr_addr p1 + c + 16).
        iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (Q1 + 1) with "W1");
          [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
        step. normp "iw_1.v37" (ptr_addr p2 + c + 16).
        iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 (Q2 + 1) with "W2");
          [reflexivity | exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
        (step; step). normp "iw_1.pr.1" (ptr_addr p1 + (c + 8) + 8). normp "iw_1.pr.2" (ptr_addr p2 + (c + 8) + 8).
        norm "iw_1.pr.3" (wrd ws1 (Q1 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F1).
        norm "iw_1.pr.4" (r - 8) ltac:(arith).
        norm "iw_1.pr.5" (wrd ws2 (Q2 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F2).
        iApply (IH (c + 8) (r - 8) (Q1 + 1) (Q2 + 1) _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsame'
                  with "W1 W2"). iIntros "W1 W2". replace (c + 8 + (r - 8)) with (c + r) by lia. iApply ("HK" with "W1 W2").
      * replace (loop_mask (wrd ws1 Q1) =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hz). close_if. step.
        assert (Hres : strncmp_res (c + r) s1 s2 = 0).
        { apply (word_zero_n s1 s2 _ _ c (wrd ws1 Q1) r H1 A1 A2 Hc Hsame X1); [|exact Hz | lia].
          rewrite {2}Exy. exact Hb. }
        eapply (s_ret registry wi ge _ _ _ _ _ _ (strncmp_res (c + r) s1 s2)); [reflexivity | reflexivity | rewrite Hres; reflexivity |].
        iApply ("HK" with "W1 W2").
  - destruct (words_differ _ _ X1 X2 Nxy) as (t & Ht & Hd).
    eapply (StrncmpLoop.fin_a registry wi ge _ _ _ s1 s2 _ _ c (wrd ws1 Q1) (wrd ws2 Q2) 8 r);
      [reflexivity | reflexivity | reflexivity | lia | lia | lia | exact H1 | exact A1 | exact A2 | |].
    { split; [lia|]. split; [exact Hsame|]. split; [lia|]. split; [lia|]. split; [exact Hb|].
      right. exists t. split; [exact Ht | right; exact Hd]. }
    iApply ("HK" with "W1 W2").
Qed.

(** Constant [blk46] holds the header block of the unaligned word loop in
    `__GI_strncmp`. *)
Definition blk46 : block := Eval vm_compute in StrncmpLoop.nblk "iw_2.L46".

(** When the second string is unaligned, each iteration merges two
    consecutive words from it to compare against one word from the first
    string. Lemma [unaligned_loop] proves that this loop returns
    [strncmp_res] (c + r) and restores both windows. *)
Lemma unaligned_loop dq1 dq2 p1 p2 b1 b2 reg1 reg2 ws1 ws2 s1 s2 c o r Q1 Q2 e Φ :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 -> 0 <= c -> 0 < o < 8 -> 0 < r < 2 ^ 64 ->
  ptr_addr p1 mod 8 + c = 8 * Q1 -> ptr_addr p2 mod 8 + c = 8 * Q2 + o -> same_upto (sbyte p1 ws1) (sbyte p2 ws2) c ->
  (forall u, 0 <= u < 8 - o -> sbyte p2 ws2 (c + u) <> 0) ->
  lookup (TAtom "iw_2.v16") e = Some (WInt (8 * o)) -> lookup (TAtom "iw_2.v20") e = Some (WInt (64 - 8 * o)) ->
  lookup (TAtom "v76") e = Some (WInt o) ->
  wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
  (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
   Φ (Ret (WInt (strncmp_res (c + r) s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strncmp (put (TAtom "iw_2.pr.1") (WPtr (mkPtr (ptr_addr p1 + c + 8) (ptr_cap p1)))
       (put (TAtom "iw_2.pr.2") (WPtr (mkPtr (wstart p2 + 8 * Q2 + 8) (ptr_cap p2)))
       (put (TAtom "iw_2.pr.4") (WInt (wrd ws1 Q1)) (put (TAtom "iw_2.pr.6") (WInt r)
       (put (TAtom "iw_2.pr.8") (WInt (wrd ws2 Q2)) e))))) [] None
       (Exec (TAtom "iw_2.L46") (b_insts blk46) (b_jump blk46))) : gexpr) {{ Φ }}.
Proof.
  intros Hs1 Hs2. facts Hs1 Hs2.
  remember (Z.to_nat (Z.of_nat (List.length ws1) - Q1)) as n eqn:Hn.
  revert c r Q1 Q2 e Hn. induction n as [|n IH];
    intros c r Q1 Q2 e Hn Hc [Ho0 Ho8] [Hr0 Hr] HQ1 HQ2 Hsame Hlo H16 H20 H76;
    destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame) as [L1 L2]; [exfalso; lia|].
  iIntros "W1 W2 HK". cbn [blk46 b_insts b_jump].
  assert (Hnz2 : forall j, 0 <= j < c + 8 - o -> sbyte p2 ws2 j <> 0).
  { intros j Hj. destruct (Z.lt_ge_cases j c).
    - destruct (Hsame j ltac:(lia)) as [E N]. congruence.
    - replace j with (c + (j - c)) by lia. apply Hlo. lia. }
  pose proof (nonzero_len _ _ _ A2 Hnz2) as L2'.
  step. normp "iw_2.v50" (wstart p2 + 8 * Q2 + 16).
  iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 (Q2 + 1) with "W2");
    [reflexivity | exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
  set (lo := wrd ws2 Q2). set (hi := wrd ws2 (Q2 + 1)). set (x := wrd ws1 Q1).
  pose proof (wrd_range ws1 Q1 F1) as X1. pose proof (wrd_range ws2 Q2 F2) as XL.
  pose proof (wrd_range ws2 (Q2 + 1) F2) as XH. pose proof (merge_range lo hi o) as XM.
  step_symbolic. step_symbolic. step_symbolic. normt (merge lo hi o) ltac:(reflexivity).
  assert (Hb : forall u, 0 <= u < 8 -> sbyte p1 ws1 (c + u) = byte_of x u /\ sbyte p2 ws2 (c + u) = byte_of (merge lo hi o) u)
    by (intros u Hu; unfold sbyte; split; [apply bt_at | apply bt_merge]; lia).
  step_symbolic. branch_symbolic. rewrite (Z.mod_small r); [|lia]. change (8 mod 2 ^ 64) with 8.
  destruct (Z.leb_spec r 8) as [Hr8|Hr8]; close_if.
  - step. branch_symbolic. close_if.
    eapply (StrncmpLoop.fin_b registry wi ge _ _ _ s1 s2 _ _ c x (merge lo hi o) 8 r);
      [reflexivity | reflexivity | reflexivity | lia | lia | lia | exact H1 | exact A1 | exact A2 | |].
    { split; [lia|]. split; [exact Hsame|]. split; [lia|]. split; [lia|]. split; [exact Hb | left; lia]. }
    iApply ("HK" with "W1 W2").
  - step. step_symbolic. (step; step). branch_symbolic. rewrite (Z.mod_small x); [|lia]. rewrite (Z.mod_small (merge lo hi o)); [|lia].
    destruct (Z.eqb_spec x (merge lo hi o)) as [Exy|Nxy]; close_if.
    + step. step_symbolic. normt (r - 8) ltac:(arith). do 4 step_symbolic. normt (loop_mask hi) ltac:(reflexivity). step_symbolic. branch_symbolic.
      rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _)).
      assert (Hhi : forall u, 0 <= u < o -> byte_of hi u = byte_of x (u + 8 - o)).
      { intros u Hu. rewrite Exy merge_byte; [|lia|lia]. replace (u + 8 - o + o <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
        f_equal. lia. }
      assert (Hsx : (forall u, 0 <= u < 8 -> byte_of x u <> 0) ->
                    same_upto (sbyte p1 ws1) (sbyte p2 ws2) (c + 8)).
      { intros Hx. apply (word_same _ _ c x (merge lo hi o) Hc Hsame Hb). intros u Hu. rewrite -Exy. auto. }
      assert (Hb' : forall u, 0 <= u < 8 - o -> sbyte p1 ws1 (c + 8 + u) = byte_of (wrd ws1 (Q1 + 1)) u /\
                                              sbyte p2 ws2 (c + 8 + u) = byte_of (shd hi o) u).
      { intros u Hu. unfold sbyte. split; [apply bt_at; lia|]. rewrite shd_byte; [|lia|lia].
        replace (u + o <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (ptr_addr p2 mod 8 + (c + 8 + u)) with (8 * (Q2 + 1) + (u + o)) by lia. rewrite -bt_word; [done|lia|lia]. }
      destruct (Z.eq_dec (loop_mask hi) 0) as [Hz|Hz].
      1: (rewrite Hz; close_if; step; step_symbolic; normt (8 - o) ltac:(arith); step_symbolic; (step; step); branch_symbolic;
        rewrite (Z.mod_small (r - 8)); [|lia]; rewrite (Z.mod_small (8 - o)); [|lia];
        destruct (Z.leb_spec (r - 8) (8 - o)) as [Hro|Hro]; close_if).
      2: { step. assert (Hsame' : same_upto (sbyte p1 ws1) (sbyte p2 ws2) (c + 8)).
           { apply Hsx. intros u Hu. destruct (Z.lt_ge_cases u (8 - o)).
             - destruct (Hb u Hu) as [_ E]. rewrite Exy -E. apply Hlo. lia.
             - rewrite Exy merge_byte; [|lia|lia]. replace (u + o <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
               apply (loop_mask_zero _ XH); [exact Hz | lia]. }
           destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame') as [L1' L2''].
           step. normp "iw_2.v94" (ptr_addr p1 + c + 16).
           iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (Q1 + 1) with "W1");
             [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
           (step; step). normp "iw_2.pr.1" (ptr_addr p1 + (c + 8) + 8). normp "iw_2.pr.2" (wstart p2 + 8 * (Q2 + 1) + 8).
           norm "iw_2.pr.4" (wrd ws1 (Q1 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F1).
           norm "iw_2.pr.6" (r - 8) ltac:(arith).
           norm "iw_2.pr.8" (wrd ws2 (Q2 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F2).
           iApply (IH (c + 8) (r - 8) (Q1 + 1) (Q2 + 1) _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                     ltac:(lia) Hsame' with "W1 W2").
           all: first [lkf H16 | lkf H20 | lkf H76
             | iIntros "W1 W2"; replace (c + 8 + (r - 8)) with (c + r) by lia; iApply ("HK" with "W1 W2")
             | intros u Hu; unfold sbyte; replace (ptr_addr p2 mod 8 + (c + 8 + u)) with (8 * (Q2 + 1) + (o + u)) by lia;
               rewrite -bt_word; [|lia|lia]; apply (loop_mask_zero _ XH); [exact Hz | lia]]. }
      2: (replace (loop_mask hi =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hz); close_if;
        step; branch_symbolic; close_if).
      (* Both ends at iw_4: the count ends within the next comparison, or hi has a zero. *)
      all: (step; do 4 step_symbolic; normt (loop_mask x) ltac:(reflexivity); step_symbolic; branch_symbolic;
  rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _));
  destruct (Z.eq_dec (loop_mask x) 0) as [Hx|Hx];
  [ rewrite Hx; close_if; step;
    let Hsame' := fresh "Hsame'" in pose proof (Hsx (proj1 (loop_mask_zero _ X1) Hx)) as Hsame';
    destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame') as [L1' L2''];
    iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (Q1 + 1) with "W1");
      [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]; iIntros "W1";
    step_symbolic; step_symbolic; step_symbolic; step_symbolic; normt (shd hi o) ltac:(unfold shd; symmetry; apply Z.lor_0_r);
    (step; step); norm "iw_2.pr.9" (shd hi o) ltac:(symmetry; apply shd_mod); norm "iw_2.pr.5" (r - 8) ltac:(arith);
    norm "iw_2.pr.3" (wrd ws1 (Q1 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F1);
    eapply (StrncmpLoop.fin_c registry wi ge _ _ s1 s2 _ _ (c + 8) (wrd ws1 (Q1 + 1)) (shd hi o) (8 - o) (r - 8));
      [reflexivity | reflexivity | reflexivity | apply wrd_range, F1 | apply Z.mod_pos_bound; lia | lia
      | exact H1 | exact A1 | exact A2 | |];
    [ split; [lia|]; split; [exact Hsame'|]; split; [lia|]; split; [lia|]; split; [exact Hb' | first [left; lia | right; destruct (loop_mask_has_zero hi XH Hz) as (z & Hz8 & Hz0);
          assert (Hzo : o <= z) by (destruct (Z.lt_ge_cases z o) as [Hlt|]; [|lia]; exfalso; rewrite Hhi in Hz0; [|lia];
            apply (proj1 (loop_mask_zero _ X1) Hx (z + 8 - o)); [lia | exact Hz0]);
          exists (z - o); split; [lia|]; unfold stop_at; rewrite shd_byte; [|lia|lia];
          replace (z - o + o <? 8) with true by (symmetry; apply Z.ltb_lt; lia); replace (z - o + o) with z by lia;
          rewrite Hz0; lia]]
    | replace (c + 8 + (r - 8)) with (c + r) by lia; iApply ("HK" with "W1 W2") ]
  | replace (loop_mask x =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hx); close_if; step;
    let Hres := fresh "Hres" in
    assert (Hres : strncmp_res (c + r) s1 s2 = 0)
      by (apply (word_zero_n s1 s2 _ _ c x r H1 A1 A2 Hc Hsame X1); [rewrite {2}Exy; exact Hb | exact Hx | lia]);
    eapply (s_ret registry wi ge _ _ _ _ _ _ (strncmp_res (c + r) s1 s2)); [reflexivity | reflexivity | rewrite Hres; reflexivity |];
    iApply ("HK" with "W1 W2") ]).
    + destruct (words_differ _ _ X1 XM Nxy) as (t & Ht & Hd).
      eapply (StrncmpLoop.fin_b registry wi ge _ _ _ s1 s2 _ _ c x (merge lo hi o) 8 r);
        [reflexivity | reflexivity | reflexivity | lia | lia | lia | exact H1 | exact A1 | exact A2 | |].
      { split; [lia|]. split; [exact Hsame|]. split; [lia|]. split; [lia|]. split; [exact Hb|].
        right. exists t. split; [exact Ht | right; exact Hd]. }
      iApply ("HK" with "W1 W2").
Qed.

End rules.
