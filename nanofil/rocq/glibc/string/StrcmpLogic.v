(** In C, `c: strcmp` can receive pointers at arbitrary byte alignments,
    and the two pointers may even alias the same string. To use 64-bit
    word comparisons safely, glibc's `__GI_strcmp`
    ([StrcmpCode](StrcmpCode.v)) first compares individual bytes until
    the first pointer reaches an 8-byte boundary, then switches to the
    aligned or unaligned word loops in [StrcmpLoop](StrcmpLoop.v).

    Two `c: strcmp` callers might pass pointers into the same string
    buffer or into read-only memory. This module proves the byte-level
    prologue, the alignment dispatch, and the entry specifications for
    `c: strcmp` so callers can share strings, recover their read
    permissions, and obtain [strcmp_res]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrcmpCode StrcmpBits StrcmpLoop.
Open Scope Z_scope.
Open Scope list_scope.

(** Module [StrcmpLogicOn] packages the `c: strcmp` entry triples over a
    given [[runtime]] R and logic instance LG0. *)
Module StrcmpLogicOn (R : Runtime) (LG0 : LogicSig R).
(** Module [SL] provides the aligned and unaligned word-loop proofs. *)
Module SL := StrcmpLoopOn R LG0.
(** Module [WS] provides the word-window string representation. *)
Module WS := SL.WS.
(** Module [LG] re-exports the program logic instance LG0. *)
Module LG := LG0.
(** Module [L] provides the nanofil language definition for LG. *)
Module L := LG.L.
Import L LG WS SL.

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
Ltac sl := eapply (s_let registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** Tactic [sf] steps past a capability `flight` check instruction. *)
Ltac sf := eapply (s_flight registry wi ge); [reflexivity | reflexivity | reflexivity |].
(** Tactic [en] enters the target basic block of a pending frame jump. *)
Ltac en := eapply (s_enter registry wi ge); [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** Tactic [sg] steps through a `goto` terminator and immediately enters
    its destination block. *)
Ltac sg := eapply (s_goto registry wi ge); en.
(** Tactic [sb] steps past a conditional `branch` instruction without
    evaluating its condition. *)
Ltac sb := eapply (s_branch registry wi ge); [reflexivity|].
(** Tactic [slk] steps past a `let` instruction that reads an earlier
    variable n whose value is given by H. *)
Ltac slk n H := eapply (s_let registry wi ge); [reflexivity | reflexivity |
  cbn [map2_option value_x]; repeat (rewrite (lookup_after_put_other _ (TAtom n)); [|reflexivity]);
  rewrite H; reflexivity | intros ?; reflexivity |].
(** Tactic [norm] rewrites the integer held by [[temporary]] name to v
    using tactic tac. *)
Ltac norm name v tac :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by tac end.
(** Tactic [normt] normalizes the integer in the newest local variable
    to v using tactic tac. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Tactic [normp] rewrites the address of the pointer held by
    [[temporary]] name to v using linear arithmetic. *)
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
    8-byte boundary, glibc loads the first 64-bit word and checks the
    low bits of the second pointer. If the second pointer is also
    aligned, control enters [aligned_loop]. Otherwise, glibc shifts the
    second string's partial first word into place, pads the missing
    high bytes with `0xff`, and either enters [unaligned_loop] or jumps
    to [fin_c] if those initial bytes already contain a NUL. *)

(** Lemma [after_bytes] verifies the transition at offset c after the
    byte loop aligns p1 to word Q1, dispatching to [aligned_loop],
    [unaligned_loop], or [fin_c]. *)
Lemma after_bytes dq1 dq2 p1 p2 b1 b2 reg1 reg2 ws1 ws2 s1 s2 c Q1 q1 q2 z1 z2 z3 e Φ :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 -> 0 <= c -> ptr_addr p1 mod 8 + c = 8 * Q1 ->
  same_upto (sbyte p1 ws1) (sbyte p2 ws2) c ->
  ptr_addr q1 = ptr_addr p1 + c -> ptr_cap q1 = ptr_cap p1 -> ptr_addr q2 = ptr_addr p2 + c -> ptr_cap q2 = ptr_cap p2 ->
  wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
  (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗ Φ (Ret (WInt (strcmp_res s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strcmp (put (TAtom "v17") z1 (put (TAtom "v16") z2 (put (TAtom "pr.1") (WPtr q1)
       (put (TAtom "pr.2") (WPtr q2) (put (TAtom "pr.3") z3 e))))) [] None (Enter (TAtom "L13") (Some (TAtom "L10"))))
       : gexpr) {{ Φ }}.
Proof.
  intros Hs1 Hs2 Hc HQ1 Hsame Hq1 Hc1 Hq2 Hc2. facts Hs1 Hs2.
  destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame) as [L1 L2].
  iIntros "W1 W2 HK". en.
  set (Q2 := (ptr_addr p2 mod 8 + c) / 8). set (o := (ptr_addr p2 mod 8 + c) mod 8).
  assert (HQ2 : ptr_addr p2 mod 8 + c = 8 * Q2 + o) by (apply Z.div_mod; lia).
  assert (Ho : 0 <= o < 8) by (apply Z.mod_pos_bound; lia). destruct Ho as [Ho0 Ho8].
  assert (Hao : (ptr_addr p2 + c) mod 8 = o).
  { replace (ptr_addr p2 + c) with (o + (wstart p2 / 8 + Q2) * 8).
    - rewrite Z_mod_plus_full. apply Z.mod_small. lia.
    - pose proof (Z.div_mod (wstart p2) 8 ltac:(lia)). lia. }
  sf. normp "v51" (ptr_addr p1 + c + 8).
  iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 Q1 with "W1");
    [reflexivity | rewrite Hc1; exact C1 | lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
  set (x := wrd ws1 Q1). pose proof (wrd_range ws1 Q1 F1) as X1.
  sl. sl. normt o ltac:(rewrite -Hao; symmetry; rewrite Hq2; apply land7; lia).
  sl. sb. rewrite (Z.mod_small o); [|lia]. rewrite ?Hc1. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eqb_spec o 0) as [Eo|Eo]; close_if.
  - en. sf. normp "iw_1.v8" (ptr_addr p2 + c + 8).
    iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 Q2 with "W2");
      [reflexivity | cbn; rewrite Hc2; exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
    sg. norm "iw_1.pr.4" (wrd ws2 Q2) ltac:(symmetry; apply Z.mod_small, wrd_range, F2).
    norm "iw_1.pr.3" x ltac:(symmetry; apply Z.mod_small; lia).
    rewrite ?Hc2. iApply (aligned_loop registry wi ge _ _ _ _ _ _ _ _ _ _ _ _ c Q1 Q2 with "W1 W2 HK"); [done | done | lia | lia | lia | done].
  - en. sf. normp "v69" (wstart p2 + 8 * Q2). sf. normp "iw_2.v10" (wstart p2 + 8 * Q2 + 8).
    iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 Q2 with "W2");
      [reflexivity | cbn; rewrite Hc2; exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
    set (lo := wrd ws2 Q2). pose proof (wrd_range ws2 Q2 F2) as XL.
    sl. normt (8 * o) ltac:(arith). sl. normt (64 - 8 * o) ltac:(arith).
    sl. sl. sl. normt (merge lo all64 o) ltac:(reflexivity).
    do 4 sl. normt (loop_mask (merge lo all64 o)) ltac:(reflexivity). sl. sb.
    pose proof (merge_range lo all64 o) as XM.
    assert (Hb : forall u, 0 <= u < 8 - o -> sbyte p1 ws1 (c + u) = byte_of x u /\
                                         sbyte p2 ws2 (c + u) = byte_of (merge lo all64 o) u).
    { intros u Hu. unfold sbyte. split; [apply bt_at; lia|]. rewrite merge_byte; [|lia|lia].
      replace (u + o <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      unfold lo. rewrite (bt_word ws2 Q2 (u + o)); [|lia|lia]. f_equal. lia. }
    destruct (Z.eq_dec (loop_mask (merge lo all64 o)) 0) as [Hz|Hz].
    + rewrite Hz. close_if. en.
      norm "iw_2.pr.5" lo ltac:(symmetry; apply Z.mod_small; lia). norm "iw_2.pr.4" x ltac:(symmetry; apply Z.mod_small; lia).
      rewrite ?Hc2. iApply (unaligned_loop registry wi ge _ _ _ _ _ _ _ _ _ _ _ _ c o Q1 Q2 with "W1 W2 HK");
        [done | done | lia | lia | lia | lia | done | | reflexivity | reflexivity].
      intros u Hu. destruct (Hb u Hu) as [_ ->]. apply (loop_mask_zero _ XM); [exact Hz | lia].
    + rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _)).
      replace (loop_mask (merge lo all64 o) =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hz).
      close_if. en.
      norm "iw_2.pr.6" (merge lo all64 o) ltac:(symmetry; apply Z.mod_small; lia).
      norm "iw_2.pr.3" x ltac:(symmetry; apply Z.mod_small; lia).
      destruct (loop_mask_has_zero _ XM Hz) as (z & Hz8 & Hz0).
      assert (Hzr : 0 <= z < 8 - o).
      { split; [lia|]. destruct (Z.lt_ge_cases z (8 - o)) as [|Hge]; [lia|]. exfalso.
        rewrite merge_byte in Hz0; [|lia|lia]. replace (z + o <? 8) with false in Hz0 by (symmetry; apply Z.ltb_ge; lia).
        rewrite byte_all64 in Hz0; [discriminate|lia]. }
      assert (Hst : stop_at (byte_of x) (byte_of (merge lo all64 o)) z).
      { unfold stop_at. rewrite Hz0. lia. }
      destruct (word_stop s1 s2 _ _ c _ _ (8 - o) H1 A1 A2 Hc Hsame ltac:(lia) Hb (ex_intro _ z (conj Hzr Hst)))
        as (jj & Hjj & Hst' & Hsj & Hres).
      eapply (fin_c registry wi ge _ _ _ _ jj); [lia | exact Hst' | exact Hsj |]. rewrite -Hres. iApply ("HK" with "W1 W2").
Qed.

(** ## The byte loop

    When the first string pointer p1 is not 8-byte aligned, glibc steps
    byte by byte until it reaches the next word boundary, at most seven
    bytes away. Each iteration loads one byte from both strings, returns
    immediately on a NUL or mismatch, and otherwise increments the
    offset i toward the alignment count in v8. *)

(** Constant [blk10] extracts the entry basic block `L10` of the byte
    comparison loop from `__GI_strcmp`. *)
Definition blk10 : block := Eval vm_compute in blk "L10".

(** Lemma [byte_loop] proves by induction on the remaining alignment
    bytes that starting at offset i returns [strcmp_res] and restores
    both string windows. *)
Lemma byte_loop dq1 dq2 p1 p2 b1 b2 reg1 reg2 ws1 ws2 s1 s2 i q1 q2 e Φ :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 -> 0 <= i <= (- ptr_addr p1) mod 8 ->
  same_upto (sbyte p1 ws1) (sbyte p2 ws2) i ->
  ptr_addr q1 = ptr_addr p1 + i -> ptr_cap q1 = ptr_cap p1 -> ptr_addr q2 = ptr_addr p2 + i -> ptr_cap q2 = ptr_cap p2 ->
  lookup (TAtom "v8") e = Some (WInt ((- ptr_addr p1) mod 8)) ->
  wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
  (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗ Φ (Ret (WInt (strcmp_res s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strcmp (put (TAtom "pr.1") (WPtr q1) (put (TAtom "pr.2") (WPtr q2) (put (TAtom "pr.3") (WInt i) e)))
       [] None (Exec (TAtom "L10") (b_insts blk10) (b_jump blk10))) : gexpr) {{ Φ }}.
Proof.
  intros Hs1 Hs2. facts Hs1 Hs2. set (n8 := (- ptr_addr p1) mod 8).
  assert (H8 : 0 <= n8 < 8) by (apply Z.mod_pos_bound; lia).
  remember (Z.to_nat (n8 - i)) as n eqn:Hn.
  revert i q1 q2 e Hn. induction n as [|n IH]; intros i q1 q2 e Hn [Hi0 Hi8] Hsame Hq1 Hc1 Hq2 Hc2 Hv8;
    destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame) as [L1 L2];
    iIntros "W1 W2 HK"; cbn [blk10 b_insts b_jump];
    sl; normt i ltac:(symmetry; apply sext_small; lia); slk "v8" Hv8; sb;
    rewrite (Z.mod_small i); try lia; rewrite (Z.mod_small n8); try lia.
  - (* i = n8: the words. *)
    replace (i <? n8) with false by (symmetry; apply Z.ltb_ge; lia). close_if.
    assert (HQ1 : ptr_addr p1 mod 8 + i = 8 * ((ptr_addr p1 mod 8 + i) / 8)).
    { replace i with n8 by lia. unfold n8. Z.div_mod_to_equations. lia. }
    iApply (after_bytes _ _ _ _ _ _ _ _ _ _ _ _ i _ q1 q2 with "W1 W2 HK"); done || lia.
  - destruct (Z.ltb_spec i n8) as [Hlt|Hge]; [|lia]. close_if. en.
    sf. normp "v20" (ptr_addr p1 + i + 1).
    iApply (wp_win_byte registry wi ge _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (ptr_addr p1 mod 8 + i)
              with "W1"); [reflexivity | rewrite Hc1; exact C1 | lia | lia | lia | lia | lia | lia |]. iIntros "W1".
    sl. normt (sbyte p1 ws1 i) ltac:(symmetry; apply sb_ub, byte_of_range).
    sf. normp "v25" (ptr_addr p2 + i + 1).
    iApply (wp_win_byte registry wi ge _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 (ptr_addr p2 mod 8 + i)
              with "W2"); [reflexivity | rewrite Hc2; exact C2 | lia | lia | lia | lia | lia | lia |]. iIntros "W2".
    sl. normt (sbyte p2 ws2 i) ltac:(symmetry; apply sb_ub, byte_of_range).
    assert (Y1 : 0 <= sbyte p1 ws1 i < 256) by apply byte_of_range.
    assert (Y2 : 0 <= sbyte p2 ws2 i < 256) by apply byte_of_range.
    set (c1 := sbyte p1 ws1 i) in *. set (c2 := sbyte p2 ws2 i) in *.
    assert (Hstop : stop_at (sbyte p1 ws1) (sbyte p2 ws2) i -> strcmp_res s1 s2 = (c1 - c2) mod 2 ^ 32).
    { intros Hst. apply strcmp_res_stop; [ | exact A1 | exact A2 | lia | exact Hsame | exact Hst].
      apply Forall_forall. intros x Hx. rewrite Forall_forall in H1. specialize (H1 x Hx). lia. }
    sl. normt ((c1 - c2) mod 2 ^ 32) ltac:(arith). sl. sb.
    rewrite (Z.mod_small c1); [|lia]. change (0 mod 2 ^ 32) with 0.
    destruct (Z.eqb_spec c1 0) as [Z1|Z1]; close_if.
    + en. sb. close_if. en.
      eapply (s_ret registry wi ge _ _ _ _ _ _ (strcmp_res s1 s2)); [reflexivity | reflexivity | |].
      { rewrite Hstop; [apply Zmod_mod | left; exact Z1]. }
      iApply ("HK" with "W1 W2").
    + en. sl. sg. sb. rewrite !Zmod_mod. change (0 mod 2 ^ 32) with 0.
      destruct (Z.eqb_spec ((c1 - c2) mod 2 ^ 32) 0) as [D|D]; close_if.
      * assert (Ec : c1 = c2) by (destruct (Z.eq_dec c1 c2); [done | exfalso; exact (byte_diff_nonzero c1 c2 Y1 Y2 n0 D)]).
        en. sl. normt (i + 1) ltac:(arith). sg. norm "pr.3" (i + 1) ltac:(arith).
        iApply (IH (i + 1) with "W1 W2 HK"); [lia | lia | | cbn; lia | done | cbn; lia | done | look Hv8].
        intros j Hj. destruct (Z.eq_dec j i) as [->|]; [split; [exact Ec | exact Z1] | apply Hsame; lia].
      * en. eapply (s_ret registry wi ge _ _ _ _ _ _ (strcmp_res s1 s2)); [reflexivity | reflexivity | |].
        { rewrite Hstop; [apply Zmod_mod | right; intros Ec; apply D; unfold c1, c2; rewrite Ec Z.sub_diag; reflexivity]. }
        iApply ("HK" with "W1 W2").
Qed.

(** ## The triples

    We now assemble the prologue and word loops into the function-level
    contract for `c: strcmp`. Direct frame execution and C function
    calls bind the formal parameters `v0` and `v2` in opposite list
    orders, so [strcmp_entry] handles both orders once and exposes the
    public [[hoare-triple|Hoare triples]] below. *)

(** Lemma [strcmp_entry] verifies `__GI_strcmp` from its entry block
    for either parameter-binding order of p1 and p2. *)
Lemma strcmp_entry dq1 dq2 p1 p2 s1 s2 e Φ :
  e = [(TAtom "v0", WPtr p1); (TAtom "v2", WPtr p2)] \/ e = [(TAtom "v2", WPtr p2); (TAtom "v0", WPtr p1)] ->
  word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗
  (word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗ Φ (Ret (WInt (strcmp_res s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strcmp e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros He. iIntros "(%b1 & %reg1 & %ws1 & %Hs1 & W1) (%b2 & %reg2 & %ws2 & %Hs2 & W2) HK". facts Hs1 Hs2.
  destruct He as [-> | ->];
    (en; sl; sl; sl; normt ((- ptr_addr p1) mod 8) ltac:(symmetry; apply neg_land7; lia);
     sg; norm "pr.3" 0 ltac:(reflexivity);
     iApply (byte_loop _ _ _ _ _ _ _ _ _ _ _ _ 0 with "W1 W2 [HK]");
       [exact Hs1 | exact Hs2 | split; [lia | apply Z.mod_pos_bound; lia] | intros j Hj; lia | lia | done | lia | done
       | reflexivity |];
     iIntros "W1 W2"; iApply ("HK" with "[W1] [W2]");
       [iApply (word_string_intro _ _ _ _ _ _ Hs1 with "W1") | iApply (word_string_intro _ _ _ _ _ _ Hs2 with "W2")]).
Qed.

(** Theorem [wp_glibc_strcmp_ws] proves the standalone specification of
    `__GI_strcmp` over two [word_string] permissions at arbitrary
    shares. *)
Lemma wp_glibc_strcmp_ws dq1 dq2 p1 p2 s1 s2 Φ :
  word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗
  (word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗ Φ (Ret (WInt (strcmp_res s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strcmp [(TAtom "v0", WPtr p1); (TAtom "v2", WPtr p2)] [] None
             (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof. apply strcmp_entry. left. reflexivity. Qed.

(** Theorem [wp_call_glibc_strcmp] lets any caller invoke `__GI_strcmp`
    by name g, returning [strcmp_res] and both [word_string]
    permissions. *)
Lemma wp_call_glibc_strcmp f e ls l r g args rest j dq1 dq2 p1 p2 s1 s2 cf' Φ :
  map_option (arg_x ge e) args = Some [WPtr p1; WPtr p2] -> find_fn ge g = Some (Defined glibc_strcmp) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) (Ret (WInt (strcmp_res s1 s2))) = Some cf' ->
  word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗
  ▷ (word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hg Hr. iIntros "H1 H2 HK".
  iApply (wp_call_bind registry wi ge _ _ _ _ _ _ _ _ _ _ _
            (mkFrame glibc_strcmp [(TAtom "v2", WPtr p2); (TAtom "v0", WPtr p1)] [] None (Enter (TAtom "start") None))
            with "[H1 H2 HK]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply (strcmp_entry with "H1 H2"); [right; reflexivity|]. iIntros "H1 H2". iExists cf'. iSplit; [done|]. iNext.
  iApply ("HK" with "H1 H2").
Qed.

End rules.
End StrcmpLogicOn.
