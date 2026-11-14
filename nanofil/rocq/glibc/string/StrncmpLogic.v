(** In C, `c: strncmp` compares at most n bytes from two strings whose
    pointers may be unaligned or aliased. To handle arbitrary alignments
    and byte limits safely, glibc's `__GI_strncmp`
    ([StrncmpCode](StrncmpCode.v)) first steps byte by byte until either
    the first pointer reaches an 8-byte boundary or n bytes have been
    checked, returning zero immediately when n is zero without reading
    memory.

    Once the first pointer is 8-byte aligned with bytes remaining,
    `c: strncmp` dispatches to the aligned or unaligned word loops in
    [StrncmpWords](StrncmpWords.v). Two callers might pass pointers into
    the same string or read-only memory, so this module proves the entry
    specifications that return both string permissions alongside
    [strncmp_res]. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrncmpCode StrcmpBits StrcmpLoop
  StrncmpBits StrncmpLoop StrncmpWords.
From Glibc Require StrcmpLoop StrncmpLoop StrncmpWords WordString.
From Glibc Require Import Fix.
From Glibc Require Import GlibcProgram GlibcSpec.
Open Scope Z_scope.
Open Scope list_scope.


(** Module [SW] provides the aligned and unaligned word-loop proofs for
    `c: strncmp`. *)
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
(** To avoid repeating boilerplate at the start of each proof, tactic
    [facts] extracts the address bounds, word lengths, and
    byte-agreement properties from both strings. *)
Ltac facts Hs1 Hs2 :=
  destruct (shape_facts _ _ _ _ _ Hs1) as (B1 & S1 & M1 & P1 & K1 & E1 & R1 & N1 & C1);
  destruct (shape_facts _ _ _ _ _ Hs2) as (B2 & S2 & M2 & P2 & K2 & E2 & R2 & N2 & C2);
  pose proof (ss_words _ _ _ _ _ Hs1) as F1; pose proof (ss_words _ _ _ _ _ Hs2) as F2;
  pose proof (ss_chars _ _ _ _ _ Hs1) as H1; pose proof (sbyte_agree _ _ _ _ _ Hs1) as A1;
  pose proof (sbyte_agree _ _ _ _ _ Hs2) as A2.

(** ## From the byte loop to the word loops

    Once the byte prologue aligns the first string's pointer to an
    8-byte boundary while bytes still remain under the limit n, glibc
    loads the first 64-bit word and checks the low bits of the second
    pointer. If the second pointer is also aligned, control enters
    `StrncmpWords.aligned_loop`. Otherwise, glibc pads the second string's partial
    first word with `0xff` and enters `StrncmpWords.unaligned_loop`, or exits
    through `StrncmpLoop.fin_c` if a NUL appears or the remaining count runs out
    within those initial bytes. *)

(** Lemma [after_bytes] verifies the alignment dispatch at offset c
    below n after the byte loop aligns p1 to word Q1. *)
Lemma after_bytes dq1 dq2 p1 p2 b1 b2 reg1 reg2 ws1 ws2 s1 s2 n c Q1 q1 q2 z1 z2 z3 z4 e Φ :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 -> 0 <= c < n -> n < 2 ^ 64 ->
  ptr_addr p1 mod 8 + c = 8 * Q1 -> same_upto (sbyte p1 ws1) (sbyte p2 ws2) c ->
  ptr_addr q1 = ptr_addr p1 + c -> ptr_cap q1 = ptr_cap p1 -> ptr_addr q2 = ptr_addr p2 + c -> ptr_cap q2 = ptr_cap p2 ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "v21") e = Some (WInt c) ->
  wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
  (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
   Φ (Ret (WInt (strncmp_res n s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strncmp (put (TAtom "v65") z1 (put (TAtom "v31") z2 (put (TAtom "v30") z3
       (put (TAtom "pr.1") (WPtr q1) (put (TAtom "pr.2") (WPtr q2) (put (TAtom "pr.3") z4 e)))))) [] None
       (Enter (TAtom "L62") (Some (TAtom "L27")))) : gexpr) {{ Φ }}.
Proof.
  intros Hs1 Hs2 [Hc Hcn] Hn HQ1 Hsame Hq1 Hc1 Hq2 Hc2 H4 H21. facts Hs1 Hs2.
  destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame) as [L1 L2].
  iIntros "W1 W2 HK". step.
  set (Q2 := (ptr_addr p2 mod 8 + c) / 8). set (o := (ptr_addr p2 mod 8 + c) mod 8).
  assert (HQ2 : ptr_addr p2 mod 8 + c = 8 * Q2 + o) by (apply Z.div_mod; lia).
  assert (Ho : 0 <= o < 8) by (apply Z.mod_pos_bound; lia). destruct Ho as [Ho0 Ho8].
  assert (Hao : (ptr_addr p2 + c) mod 8 = o).
  { replace (ptr_addr p2 + c) with (o + (wstart p2 / 8 + Q2) * 8).
    - rewrite Z_mod_plus_full. apply Z.mod_small. lia.
    - pose proof (Z.div_mod (wstart p2) 8 ltac:(lia)). lia. }
  step. normp "v71" (ptr_addr p1 + c + 8).
  iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 Q1 with "W1");
    [reflexivity | rewrite Hc1; exact C1 | lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
  set (x := wrd ws1 Q1). pose proof (wrd_range ws1 Q1 F1) as X1.
  step_symbolic. step_symbolic. normt o ltac:(rewrite -Hao; symmetry; rewrite Hq2; apply land7; lia).
  step_symbolic. branch_symbolic. rewrite (Z.mod_small o); [|lia]. rewrite ?Hc1. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eqb_spec o 0) as [Eo|Eo]; close_if.
  - step. step_symbolic. normt (n - c) ltac:(arith). step. normp "iw_1.v10" (ptr_addr p2 + c + 8).
    iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 Q2 with "W2");
      [reflexivity | cbn; rewrite Hc2; exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
    (step; step). norm "iw_1.pr.5" (wrd ws2 Q2) ltac:(symmetry; apply Z.mod_small, wrd_range, F2).
    norm "iw_1.pr.4" (n - c) ltac:(arith). norm "iw_1.pr.3" x ltac:(symmetry; apply Z.mod_small; lia).
    rewrite ?Hc2. iApply (StrncmpWords.aligned_loop registry wi ge _ _ _ _ _ _ _ _ _ _ _ _ c (n - c) Q1 Q2 with "W1 W2");
      [done | done | lia | lia | lia | lia | done |].
    iIntros "W1 W2". replace (c + (n - c)) with n by lia. iApply ("HK" with "W1 W2").
  - step. step. normp "v92" (wstart p2 + 8 * Q2). step_symbolic. normt (n - c) ltac:(arith).
    step. normp "iw_2.v12" (wstart p2 + 8 * Q2 + 8).
    iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 Q2 with "W2");
      [reflexivity | cbn; rewrite Hc2; exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
    set (lo := wrd ws2 Q2). pose proof (wrd_range ws2 Q2 F2) as XL.
    step_symbolic. normt (8 * o) ltac:(arith). step_symbolic. normt (64 - 8 * o) ltac:(arith).
    step_symbolic. step_symbolic. step_symbolic. normt (merge lo all64 o) ltac:(reflexivity).
    do 4 step_symbolic. normt (loop_mask (merge lo all64 o)) ltac:(reflexivity). step_symbolic. branch_symbolic.
    pose proof (merge_range lo all64 o) as XM.
    assert (Hb : forall u, 0 <= u < 8 - o -> sbyte p1 ws1 (c + u) = byte_of x u /\
                                         sbyte p2 ws2 (c + u) = byte_of (merge lo all64 o) u).
    { intros u Hu. unfold sbyte. split; [apply bt_at; lia|]. rewrite merge_byte; [|lia|lia].
      replace (u + o <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      unfold lo. rewrite (bt_word ws2 Q2 (u + o)); [|lia|lia]. f_equal. lia. }
    destruct (Z.eq_dec (loop_mask (merge lo all64 o)) 0) as [Hz|Hz].
    + rewrite Hz. close_if. step. step_symbolic. normt (8 - o) ltac:(arith). step_symbolic. (step; step). branch_symbolic.
      rewrite (Z.mod_small (n - c)); [|lia]. rewrite (Z.mod_small (8 - o)); [|lia].
      destruct (Z.ltb_spec (8 - o) (n - c)) as [Hro|Hro]; close_if.
      * step. norm "iw_2.pr.8" lo ltac:(symmetry; apply Z.mod_small; lia).
        norm "iw_2.pr.6" (n - c) ltac:(arith). norm "iw_2.pr.4" x ltac:(symmetry; apply Z.mod_small; lia).
        rewrite ?Hc2. iApply (StrncmpWords.unaligned_loop registry wi ge _ _ _ _ _ _ _ _ _ _ _ _ c o (n - c) Q1 Q2 with "W1 W2");
          [done | done | lia | lia | lia | lia | lia | done | | reflexivity | reflexivity | reflexivity |].
        { intros u Hu. destruct (Hb u Hu) as [_ ->]. apply (loop_mask_zero _ XM); [exact Hz | lia]. }
        iIntros "W1 W2". replace (c + (n - c)) with n by lia. iApply ("HK" with "W1 W2").
      * step. norm "iw_2.pr.9" (merge lo all64 o) ltac:(symmetry; apply Z.mod_small; lia).
        norm "iw_2.pr.5" (n - c) ltac:(arith). norm "iw_2.pr.3" x ltac:(symmetry; apply Z.mod_small; lia).
        eapply (StrncmpLoop.fin_c registry wi ge _ _ s1 s2 _ _ c x (merge lo all64 o) (8 - o) (n - c));
          [reflexivity | reflexivity | reflexivity | lia | lia | lia | exact H1 | exact A1 | exact A2 | |].
        { split; [lia|]. split; [exact Hsame|]. split; [lia|]. split; [lia|]. split; [exact Hb | left; lia]. }
        replace (c + (n - c)) with n by lia. iApply ("HK" with "W1 W2").
    + rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _)).
      replace (loop_mask (merge lo all64 o) =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hz).
      close_if. step. branch_symbolic. close_if. step.
      norm "iw_2.pr.9" (merge lo all64 o) ltac:(symmetry; apply Z.mod_small; lia).
      norm "iw_2.pr.5" (n - c) ltac:(arith). norm "iw_2.pr.3" x ltac:(symmetry; apply Z.mod_small; lia).
      destruct (loop_mask_has_zero _ XM Hz) as (z & Hz8 & Hz0).
      assert (Hzr : 0 <= z < 8 - o).
      { split; [lia|]. destruct (Z.lt_ge_cases z (8 - o)) as [|Hge]; [lia|]. exfalso.
        rewrite merge_byte in Hz0; [|lia|lia]. replace (z + o <? 8) with false in Hz0 by (symmetry; apply Z.ltb_ge; lia).
        rewrite byte_all64 in Hz0; [discriminate|lia]. }
      eapply (StrncmpLoop.fin_c registry wi ge _ _ s1 s2 _ _ c x (merge lo all64 o) (8 - o) (n - c));
        [reflexivity | reflexivity | reflexivity | lia | lia | lia | exact H1 | exact A1 | exact A2 | |].
      { split; [lia|]. split; [exact Hsame|]. split; [lia|]. split; [lia|]. split; [exact Hb|].
        right. exists z. split; [exact Hzr|]. unfold stop_at. rewrite Hz0. lia. }
      replace (c + (n - c)) with n by lia. iApply ("HK" with "W1 W2").
Qed.

(** ## The byte loop

    When the first string pointer p1 is not 8-byte aligned, glibc steps
    byte by byte up to the minimum of n and the distance to the next
    word boundary. If n bytes are reached first, it returns zero;
    otherwise it compares one byte from each string, exits on a NUL or
    mismatch, or advances i toward the bound m. *)

(** Constant [blk24] holds the header block of the byte-by-byte prologue
    loop in `__GI_strncmp`. *)
Definition blk24 : block := Eval vm_compute in StrncmpLoop.nblk "L24".

(** Lemma [byte_loop] proves by induction on the remaining prologue
    bytes that starting at offset i returns [strncmp_res] n and restores
    both windows. *)
Lemma byte_loop dq1 dq2 p1 p2 b1 b2 reg1 reg2 ws1 ws2 s1 s2 n i q1 q2 e Φ :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 -> 0 <= n < 2 ^ 64 ->
  0 <= i <= Z.min ((- ptr_addr p1) mod 8) n -> same_upto (sbyte p1 ws1) (sbyte p2 ws2) i ->
  ptr_addr q1 = ptr_addr p1 + i -> ptr_cap q1 = ptr_cap p1 -> ptr_addr q2 = ptr_addr p2 + i -> ptr_cap q2 = ptr_cap p2 ->
  lookup (TAtom "v21") e = Some (WInt (Z.min ((- ptr_addr p1) mod 8) n)) -> lookup (TAtom "v4") e = Some (WInt n) ->
  wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
  (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
   Φ (Ret (WInt (strncmp_res n s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strncmp (put (TAtom "pr.1") (WPtr q1) (put (TAtom "pr.2") (WPtr q2) (put (TAtom "pr.3") (WInt i) e)))
       [] None (Exec (TAtom "L24") (b_insts blk24) (b_jump blk24))) : gexpr) {{ Φ }}.
Proof.
  intros Hs1 Hs2 [Hn0 Hn]. facts Hs1 Hs2. set (n8 := (- ptr_addr p1) mod 8). set (m := Z.min n8 n).
  assert (H8 : 0 <= n8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hm : 0 <= m <= n /\ m <= n8) by lia.
  remember (Z.to_nat (m - i)) as k eqn:Hk.
  revert i q1 q2 e Hk. induction k as [|k IH]; intros i q1 q2 e Hk [Hi0 Him] Hsame Hq1 Hc1 Hq2 Hc2 H21 H4;
    destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame) as [L1 L2];
    iIntros "W1 W2 HK"; cbn [blk24 b_insts b_jump];
    step_symbolic; normt i ltac:(symmetry; apply sext_small; lia); step_symbolic; branch_symbolic;
    rewrite (Z.mod_small i); try lia; rewrite (Z.mod_small m); try lia.
  - (* i = m: the count's end, or the words. *)
    replace (i <? m) with false by (symmetry; apply Z.ltb_ge; lia). close_if. step. step_symbolic. branch_symbolic.
    rewrite (Z.mod_small m); [|lia]. rewrite (Z.mod_small n); [|lia].
    destruct (Z.eqb_spec m n) as [Emn|Emn]; close_if.
    + step. eapply (s_ret registry wi ge _ _ _ _ _ _ (strncmp_res n s1 s2)); [reflexivity | reflexivity | |].
      { symmetry. apply (strncmp_same _ _ (sbyte p1 ws1) (sbyte p2 ws2)); [exact H1 | exact A1 | exact A2 | lia |].
        replace n with i by lia. exact Hsame. }
      iApply ("HK" with "W1 W2").
    + assert (HQ1 : ptr_addr p1 mod 8 + i = 8 * ((ptr_addr p1 mod 8 + i) / 8)).
      { replace i with n8 by lia. unfold n8. Z.div_mod_to_equations. lia. }
      iApply (after_bytes _ _ _ _ _ _ _ _ _ _ _ _ n i _ q1 q2 with "W1 W2 HK"); try done; try lia.
      replace i with m by lia. exact H21.
  - destruct (Z.ltb_spec i m) as [Hlt|Hge]; [|lia]. close_if. step.
    step. normp "v34" (ptr_addr p1 + i + 1).
    iApply (wp_win_byte registry wi ge _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (ptr_addr p1 mod 8 + i)
              with "W1"); [reflexivity | rewrite Hc1; exact C1 | lia | lia | lia | lia | lia | lia |]. iIntros "W1".
    step_symbolic. normt (sbyte p1 ws1 i) ltac:(symmetry; apply sb_ub, byte_of_range).
    step. normp "v39" (ptr_addr p2 + i + 1).
    iApply (wp_win_byte registry wi ge _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 (ptr_addr p2 mod 8 + i)
              with "W2"); [reflexivity | rewrite Hc2; exact C2 | lia | lia | lia | lia | lia | lia |]. iIntros "W2".
    step_symbolic. normt (sbyte p2 ws2 i) ltac:(symmetry; apply sb_ub, byte_of_range).
    assert (Y1 : 0 <= sbyte p1 ws1 i < 256) by apply byte_of_range.
    assert (Y2 : 0 <= sbyte p2 ws2 i < 256) by apply byte_of_range.
    set (c1 := sbyte p1 ws1 i) in *. set (c2 := sbyte p2 ws2 i) in *.
    assert (Hstop : stop_at (sbyte p1 ws1) (sbyte p2 ws2) i -> strncmp_res n s1 s2 = (c1 - c2) mod 2 ^ 32).
    { intros Hst. apply strncmp_stop; [exact H1 | exact A1 | exact A2 | lia | exact Hsame | exact Hst]. }
    step_symbolic. normt ((c1 - c2) mod 2 ^ 32) ltac:(arith). step_symbolic. branch_symbolic.
    rewrite (Z.mod_small c1); [|lia]. change (0 mod 2 ^ 32) with 0.
    destruct (Z.eqb_spec c1 0) as [Z1|Z1]; close_if.
    + step. branch_symbolic. close_if. step.
      eapply (s_ret registry wi ge _ _ _ _ _ _ (strncmp_res n s1 s2)); [reflexivity | reflexivity | |].
      { rewrite Hstop; [apply Zmod_mod | left; exact Z1]. }
      iApply ("HK" with "W1 W2").
    + step. step_symbolic. (step; step). branch_symbolic. rewrite !Zmod_mod. change (0 mod 2 ^ 32) with 0.
      destruct (Z.eqb_spec ((c1 - c2) mod 2 ^ 32) 0) as [D|D]; close_if.
      * assert (Ec : c1 = c2) by (destruct (Z.eq_dec c1 c2); [done | exfalso; exact (byte_diff_nonzero c1 c2 Y1 Y2 n0 D)]).
        step. step_symbolic. normt (i + 1) ltac:(arith). (step; step). norm "pr.3" (i + 1) ltac:(arith).
        iApply (IH (i + 1) with "W1 W2 HK"); [lia | lia | | cbn; lia | done | cbn; lia | done | lkf H21 | lkf H4].
        intros j Hj. destruct (Z.eq_dec j i) as [->|]; [split; [exact Ec | exact Z1] | apply Hsame; lia].
      * step. eapply (s_ret registry wi ge _ _ _ _ _ _ (strncmp_res n s1 s2)); [reflexivity | reflexivity | |].
        { rewrite Hstop; [apply Zmod_mod | right; intros Ec; apply D; unfold c1, c2; rewrite Ec Z.sub_diag; reflexivity]. }
        iApply ("HK" with "W1 W2").
Qed.

(** ## The triples

    We now combine the byte prologue and word loops into the
    function-level contract for `c: strncmp`. Direct frame execution and
    C function calls bind the formal parameters `v0`, `v2`, and `v4` in
    opposite list orders, so [strncmp_entry] handles both orders once
    and exposes the public [[hoare-triple|Hoare triples]] below. *)

(** Lemma [strncmp_entry] verifies `__GI_strncmp` from its entry block
    for either parameter-binding order of p1, p2, and n. *)
Lemma strncmp_entry dq1 dq2 p1 p2 s1 s2 n e Φ :
  0 <= n < 2 ^ 64 ->
  e = [(TAtom "v0", WPtr p1); (TAtom "v2", WPtr p2); (TAtom "v4", WInt n)] \/
  e = [(TAtom "v4", WInt n); (TAtom "v2", WPtr p2); (TAtom "v0", WPtr p1)] ->
  word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗
  (word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗ Φ (Ret (WInt (strncmp_res n s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strncmp e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hn He. iIntros "(%b1 & %reg1 & %ws1 & %Hs1 & W1) (%b2 & %reg2 & %ws2 & %Hs2 & W2) HK". facts Hs1 Hs2.
  set (n8 := (- ptr_addr p1) mod 8). assert (H8 : 0 <= n8 < 8) by (apply Z.mod_pos_bound; lia).
  iAssert (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
           Φ (Ret (WInt (strncmp_res n s1 s2))))%I with "[HK]" as "HK".
  { iIntros "W1 W2". iApply ("HK" with "[W1] [W2]");
      [iApply (word_string_intro _ _ _ _ _ _ Hs1 with "W1") | iApply (word_string_intro _ _ _ _ _ _ Hs2 with "W2")]. }
  destruct He as [-> | ->];
    (step; step_symbolic; step_symbolic; step_symbolic; normt n8 ltac:(symmetry; apply neg_land7; lia); step_symbolic; branch_symbolic;
     rewrite (Z.mod_small n8); [|lia]; rewrite (Z.mod_small n); [|lia];
     destruct (Z.ltb_spec n8 n) as [Hlt|Hge]; close_if;
     [step | step; (step; step)]; (step; step); norm "v21" (Z.min n8 n) ltac:(arith); norm "pr.3" 0 ltac:(reflexivity);
     (iApply (byte_loop _ _ _ _ _ _ _ _ _ _ _ _ n 0 with "W1 W2 HK");
       [exact Hs1 | exact Hs2 | lia | lia | intros j Hj; lia | lia | done | lia | done | reflexivity | reflexivity])).
Qed.

(** Theorem [wp_glibc_strncmp_ws] proves the standalone specification of
    `__GI_strncmp` over two [word_string] permissions and any limit n
    below 2^64. *)
Lemma wp_glibc_strncmp_ws dq1 dq2 p1 p2 s1 s2 n Φ :
  0 <= n < 2 ^ 64 ->
  word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗
  (word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗ Φ (Ret (WInt (strncmp_res n s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strncmp [(TAtom "v0", WPtr p1); (TAtom "v2", WPtr p2); (TAtom "v4", WInt n)] [] None
             (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof. intros Hn. apply strncmp_entry; [exact Hn | left; reflexivity]. Qed.

(** Bounded comparison preserves both strings and records its limit as a pure premise. *)
Definition strncmp_spec : fspec Σ :=
  FSpec (dfrac * dfrac * ptr * ptr * list Z * list Z * Z)
    (fun '(_, _, p1, p2, _, _, n) => [WPtr p1; WPtr p2; WInt n])
    (fun '(dq1, dq2, p1, p2, s1, s2, n) =>
      ⌜0 <= n < 2 ^ 64⌝ ∗ word_string dq1 p1 s1 ∗ word_string dq2 p2 s2)%I
    (fun '(dq1, dq2, p1, p2, s1, s2, n) v =>
      ⌜v = Ret (WInt (strncmp_res n s1 s2))⌝ ∗ word_string dq1 p1 s1 ∗ word_string dq2 p2 s2)%I.

(** The bounded entry proof supplies the named comparison contract. *)
Lemma strncmp_spec_valid g : find_fn ge g = Some (Defined glibc_strncmp) ->
  HasSpec registry wi ge g strncmp_spec.
Proof.
  intros Hg [[[[[[dq1 dq2] p1] p2] s1] s2] n]. exists glibc_strncmp. split; [exact Hg|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn in Hfr. injection Hfr as <-. cbn [fs_pre fs_post strncmp_spec].
  iIntros "(%Hn & H1 & H2) HK". iApply (strncmp_entry with "H1 H2"); [exact Hn | right; reflexivity|].
  iIntros "H1 H2". iApply "HK". by iFrame.
Qed.

(** Linked callers supply strncmp's definition through the program context. *)
#[global] Instance strncmp_has_spec n `{!Defines ge n glibc_strncmp} :
  HasSpec registry wi ge (TAtom n) strncmp_spec.
Proof. apply strncmp_spec_valid. apply defines. Qed.

(** Theorem [wp_call_glibc_strncmp] lets any caller invoke
    `__GI_strncmp` by name g, returning [strncmp_res] n and both
    [word_string] permissions. *)
Lemma wp_call_glibc_strncmp f e ls l r g args rest j dq1 dq2 p1 p2 s1 s2 n cf' Φ :
  0 <= n < 2 ^ 64 ->
  map_option (arg_x ge e) args = Some [WPtr p1; WPtr p2; WInt n] -> find_fn ge g = Some (Defined glibc_strncmp) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) (Ret (WInt (strncmp_res n s1 s2))) = Some cf' ->
  word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗
  ▷ (word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hn Hx Hg Hr. iIntros "H1 H2 HK".
  pose proof (strncmp_spec_valid g Hg) as Hspec.
  iApply (wp_call_spec registry wi ge g strncmp_spec (dq1, dq2, p1, p2, s1, s2, n) with "[H1 H2]");
    [exact Hx | by iFrame |].
  iIntros (v) "(-> & H1 & H2)". iExists cf'. iSplit; [done|].
  iNext. iApply ("HK" with "H1 H2").
Qed.

End rules.
