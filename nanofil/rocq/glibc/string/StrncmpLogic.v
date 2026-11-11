(** glibc's own `strncmp` (`__GI_strncmp`, StrncmpCode.v) over two
    [word_string]s (WordString.v) at any shares, aliased or not, and any
    count n below 2^64: [wp_glibc_strncmp_ws] for a frame of it, and
    [wp_call_glibc_strncmp] for a call of any module whose function at
    the called name is it. The caller gets StrncmpBits.v's
    [strncmp_res] and both strings back.

    glibc's strncmp first compares bytes until the first string's
    pointer is 8-aligned or n bytes are compared, whichever comes first
    ([byte_loop]); a NUL in the first string or a difference returns
    their difference ([strncmp_stop]), and a count that ends there
    returns 0 ([strncmp_same]), so a count of 0 reads no memory. It
    then reads the first string's word and tests the second string's
    alignment ([after_bytes]): an aligned second string goes to
    StrncmpWords.v's [aligned_loop]; an unaligned one has its first
    word's bytes from the pointer, padded with 0xff, tested for a NUL,
    and goes to [unaligned_loop] or, with one or with a count that ends
    within them, to the last comparison [fin_c]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrncmpCode StrcmpBits StrcmpLoop
  StrncmpBits StrncmpLoop StrncmpWords.
Open Scope Z_scope.
Open Scope list_scope.

(** The triples over the [[runtime]] R and the Logic instance LG0. *)
Module StrncmpLogicOn (R : Runtime) (LG0 : LogicSig R).
(** The word loops over R and LG0. *)
Module SW := StrncmpWordsOn R LG0.
(** The last comparisons. *)
Module SN := SW.SN.
(** StrcmpLoop.v's steps and reads. *)
Module SL := SN.SL.
(** Strings' windows. *)
Module WS := SL.WS.
(** The Logic instance. *)
Module LG := LG0.
(** Its language. *)
Module L := LG.L.
Import L LG WS SL.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** StrcmpLoop.v's steps: a let, its value whole. *)
Ltac sl := eapply (s_let registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** A let that reads the abstract environment ([vxf]). *)
Ltac sv := eapply (s_let registry wi ge); [reflexivity | reflexivity | vxf | intros ?; reflexivity |].
(** A flight. *)
Ltac sf := eapply (s_flight registry wi ge); [reflexivity | reflexivity | reflexivity |].
(** Entering the block a frame is entering. *)
Ltac en := eapply (s_enter registry wi ge); [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** A goto and the block it enters. *)
Ltac sg := eapply (s_goto registry wi ge); en.
(** A branch, its condition left whole. *)
Ltac sb := eapply (s_branch registry wi ge); [reflexivity|].
(** Replace the integer the temporary name holds by v, proved by tac. *)
Ltac norm name v tac :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by tac end.
(** Replace the integer the newest temporary holds by v, proved by tac. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Replace the address of the pointer the temporary name holds by v. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.
(** The arithmetic of the shapes Hs1 and Hs2 of the two strings, and
    the agreement of their bytes. *)
Ltac facts Hs1 Hs2 :=
  destruct (shape_facts _ _ _ _ _ Hs1) as (B1 & S1 & M1 & P1 & K1 & E1 & R1 & N1 & C1);
  destruct (shape_facts _ _ _ _ _ Hs2) as (B2 & S2 & M2 & P2 & K2 & E2 & R2 & N2 & C2);
  pose proof (ss_words _ _ _ _ _ Hs1) as F1; pose proof (ss_words _ _ _ _ _ Hs2) as F2;
  pose proof (ss_chars _ _ _ _ _ Hs1) as H1; pose proof (sbyte_agree _ _ _ _ _ Hs1) as A1;
  pose proof (sbyte_agree _ _ _ _ _ Hs2) as A2.

(** ## From the byte loop to the word loops *)

(** The byte loop has ended at c, below the count n, where the first
    string's bytes start its word Q1: pr.1 and pr.2 are q1 and q2, c
    bytes into the strings, whose bytes before c agree and are not 0.
    glibc reads the first string's word and goes on by the second's
    alignment. *)
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
  iIntros "W1 W2 HK". en.
  set (Q2 := (ptr_addr p2 mod 8 + c) / 8). set (o := (ptr_addr p2 mod 8 + c) mod 8).
  assert (HQ2 : ptr_addr p2 mod 8 + c = 8 * Q2 + o) by (apply Z.div_mod; lia).
  assert (Ho : 0 <= o < 8) by (apply Z.mod_pos_bound; lia). destruct Ho as [Ho0 Ho8].
  assert (Hao : (ptr_addr p2 + c) mod 8 = o).
  { replace (ptr_addr p2 + c) with (o + (wstart p2 / 8 + Q2) * 8).
    - rewrite Z_mod_plus_full. apply Z.mod_small. lia.
    - pose proof (Z.div_mod (wstart p2) 8 ltac:(lia)). lia. }
  sf. normp "v71" (ptr_addr p1 + c + 8).
  iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 Q1 with "W1");
    [reflexivity | rewrite Hc1; exact C1 | lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
  set (x := wrd ws1 Q1). pose proof (wrd_range ws1 Q1 F1) as X1.
  sl. sl. normt o ltac:(rewrite -Hao; symmetry; rewrite Hq2; apply land7; lia).
  sl. sb. rewrite (Z.mod_small o); [|lia]. rewrite ?Hc1. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eqb_spec o 0) as [Eo|Eo]; close_if.
  - en. sv. normt (n - c) ltac:(arith). sf. normp "iw_1.v10" (ptr_addr p2 + c + 8).
    iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 Q2 with "W2");
      [reflexivity | cbn; rewrite Hc2; exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
    sg. norm "iw_1.pr.5" (wrd ws2 Q2) ltac:(symmetry; apply Z.mod_small, wrd_range, F2).
    norm "iw_1.pr.4" (n - c) ltac:(arith). norm "iw_1.pr.3" x ltac:(symmetry; apply Z.mod_small; lia).
    rewrite ?Hc2. iApply (SW.aligned_loop registry wi ge _ _ _ _ _ _ _ _ _ _ _ _ c (n - c) Q1 Q2 with "W1 W2");
      [done | done | lia | lia | lia | lia | done |].
    iIntros "W1 W2". replace (c + (n - c)) with n by lia. iApply ("HK" with "W1 W2").
  - en. sf. normp "v92" (wstart p2 + 8 * Q2). sv. normt (n - c) ltac:(arith).
    sf. normp "iw_2.v12" (wstart p2 + 8 * Q2 + 8).
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
    + rewrite Hz. close_if. en. sl. normt (8 - o) ltac:(arith). sl. sg. sb.
      rewrite (Z.mod_small (n - c)); [|lia]. rewrite (Z.mod_small (8 - o)); [|lia].
      destruct (Z.ltb_spec (8 - o) (n - c)) as [Hro|Hro]; close_if.
      * en. norm "iw_2.pr.8" lo ltac:(symmetry; apply Z.mod_small; lia).
        norm "iw_2.pr.6" (n - c) ltac:(arith). norm "iw_2.pr.4" x ltac:(symmetry; apply Z.mod_small; lia).
        rewrite ?Hc2. iApply (SW.unaligned_loop registry wi ge _ _ _ _ _ _ _ _ _ _ _ _ c o (n - c) Q1 Q2 with "W1 W2");
          [done | done | lia | lia | lia | lia | lia | done | | reflexivity | reflexivity | reflexivity |].
        { intros u Hu. destruct (Hb u Hu) as [_ ->]. apply (loop_mask_zero _ XM); [exact Hz | lia]. }
        iIntros "W1 W2". replace (c + (n - c)) with n by lia. iApply ("HK" with "W1 W2").
      * en. norm "iw_2.pr.9" (merge lo all64 o) ltac:(symmetry; apply Z.mod_small; lia).
        norm "iw_2.pr.5" (n - c) ltac:(arith). norm "iw_2.pr.3" x ltac:(symmetry; apply Z.mod_small; lia).
        eapply (SN.fin_c registry wi ge _ _ s1 s2 _ _ c x (merge lo all64 o) (8 - o) (n - c));
          [reflexivity | reflexivity | reflexivity | lia | lia | lia | exact H1 | exact A1 | exact A2 | |].
        { split; [lia|]. split; [exact Hsame|]. split; [lia|]. split; [lia|]. split; [exact Hb | left; lia]. }
        replace (c + (n - c)) with n by lia. iApply ("HK" with "W1 W2").
    + rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _)).
      replace (loop_mask (merge lo all64 o) =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hz).
      close_if. en. sb. close_if. en.
      norm "iw_2.pr.9" (merge lo all64 o) ltac:(symmetry; apply Z.mod_small; lia).
      norm "iw_2.pr.5" (n - c) ltac:(arith). norm "iw_2.pr.3" x ltac:(symmetry; apply Z.mod_small; lia).
      destruct (loop_mask_has_zero _ XM Hz) as (z & Hz8 & Hz0).
      assert (Hzr : 0 <= z < 8 - o).
      { split; [lia|]. destruct (Z.lt_ge_cases z (8 - o)) as [|Hge]; [lia|]. exfalso.
        rewrite merge_byte in Hz0; [|lia|lia]. replace (z + o <? 8) with false in Hz0 by (symmetry; apply Z.ltb_ge; lia).
        rewrite byte_all64 in Hz0; [discriminate|lia]. }
      eapply (SN.fin_c registry wi ge _ _ s1 s2 _ _ c x (merge lo all64 o) (8 - o) (n - c));
        [reflexivity | reflexivity | reflexivity | lia | lia | lia | exact H1 | exact A1 | exact A2 | |].
      { split; [lia|]. split; [exact Hsame|]. split; [lia|]. split; [lia|]. split; [exact Hb|].
        right. exists z. split; [exact Hzr|]. unfold stop_at. rewrite Hz0. lia. }
      replace (c + (n - c)) with n by lia. iApply ("HK" with "W1 W2").
Qed.

(** ## The byte loop *)

(** The byte loop's block. *)
Definition blk24 : block := Eval vm_compute in SN.nblk "L24".

(** The byte loop at i, at most the bytes m to the first string's word
    boundary or the count n, whichever is first, which v21 holds: pr.1
    and pr.2 are q1 and q2, i bytes into the strings, whose bytes before
    i agree and are not 0. strncmp returns [strncmp_res] n and hands
    both windows back. *)
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
    sl; normt i ltac:(symmetry; apply sext_small; lia); sv; sb;
    rewrite (Z.mod_small i); try lia; rewrite (Z.mod_small m); try lia.
  - (* i = m: the count's end, or the words. *)
    replace (i <? m) with false by (symmetry; apply Z.ltb_ge; lia). close_if. en. sv. sb.
    rewrite (Z.mod_small m); [|lia]. rewrite (Z.mod_small n); [|lia].
    destruct (Z.eqb_spec m n) as [Emn|Emn]; close_if.
    + en. eapply (s_ret registry wi ge _ _ _ _ _ _ (strncmp_res n s1 s2)); [reflexivity | reflexivity | |].
      { symmetry. apply (strncmp_same _ _ (sbyte p1 ws1) (sbyte p2 ws2)); [exact H1 | exact A1 | exact A2 | lia |].
        replace n with i by lia. exact Hsame. }
      iApply ("HK" with "W1 W2").
    + assert (HQ1 : ptr_addr p1 mod 8 + i = 8 * ((ptr_addr p1 mod 8 + i) / 8)).
      { replace i with n8 by lia. unfold n8. Z.div_mod_to_equations. lia. }
      iApply (after_bytes _ _ _ _ _ _ _ _ _ _ _ _ n i _ q1 q2 with "W1 W2 HK"); try done; try lia.
      replace i with m by lia. exact H21.
  - destruct (Z.ltb_spec i m) as [Hlt|Hge]; [|lia]. close_if. en.
    sf. normp "v34" (ptr_addr p1 + i + 1).
    iApply (wp_win_byte registry wi ge _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (ptr_addr p1 mod 8 + i)
              with "W1"); [reflexivity | rewrite Hc1; exact C1 | lia | lia | lia | lia | lia | lia |]. iIntros "W1".
    sl. normt (sbyte p1 ws1 i) ltac:(symmetry; apply sb_ub, byte_of_range).
    sf. normp "v39" (ptr_addr p2 + i + 1).
    iApply (wp_win_byte registry wi ge _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 (ptr_addr p2 mod 8 + i)
              with "W2"); [reflexivity | rewrite Hc2; exact C2 | lia | lia | lia | lia | lia | lia |]. iIntros "W2".
    sl. normt (sbyte p2 ws2 i) ltac:(symmetry; apply sb_ub, byte_of_range).
    assert (Y1 : 0 <= sbyte p1 ws1 i < 256) by apply byte_of_range.
    assert (Y2 : 0 <= sbyte p2 ws2 i < 256) by apply byte_of_range.
    set (c1 := sbyte p1 ws1 i) in *. set (c2 := sbyte p2 ws2 i) in *.
    assert (Hstop : stop_at (sbyte p1 ws1) (sbyte p2 ws2) i -> strncmp_res n s1 s2 = (c1 - c2) mod 2 ^ 32).
    { intros Hst. apply strncmp_stop; [exact H1 | exact A1 | exact A2 | lia | exact Hsame | exact Hst]. }
    sl. normt ((c1 - c2) mod 2 ^ 32) ltac:(arith). sl. sb.
    rewrite (Z.mod_small c1); [|lia]. change (0 mod 2 ^ 32) with 0.
    destruct (Z.eqb_spec c1 0) as [Z1|Z1]; close_if.
    + en. sb. close_if. en.
      eapply (s_ret registry wi ge _ _ _ _ _ _ (strncmp_res n s1 s2)); [reflexivity | reflexivity | |].
      { rewrite Hstop; [apply Zmod_mod | left; exact Z1]. }
      iApply ("HK" with "W1 W2").
    + en. sl. sg. sb. rewrite !Zmod_mod. change (0 mod 2 ^ 32) with 0.
      destruct (Z.eqb_spec ((c1 - c2) mod 2 ^ 32) 0) as [D|D]; close_if.
      * assert (Ec : c1 = c2) by (destruct (Z.eq_dec c1 c2); [done | exfalso; exact (byte_diff_nonzero c1 c2 Y1 Y2 n0 D)]).
        en. sl. normt (i + 1) ltac:(arith). sg. norm "pr.3" (i + 1) ltac:(arith).
        iApply (IH (i + 1) with "W1 W2 HK"); [lia | lia | | cbn; lia | done | cbn; lia | done | lkf H21 | lkf H4].
        intros j Hj. destruct (Z.eq_dec j i) as [->|]; [split; [exact Ec | exact Z1] | apply Hsame; lia].
      * en. eapply (s_ret registry wi ge _ _ _ _ _ _ (strncmp_res n s1 s2)); [reflexivity | reflexivity | |].
        { rewrite Hstop; [apply Zmod_mod | right; intros Ec; apply D; unfold c1, c2; rewrite Ec Z.sub_diag; reflexivity]. }
        iApply ("HK" with "W1 W2").
Qed.

(** ## The triples *)

(** glibc's strncmp from its entry, with v0, v2 and v4 bound to p1, p2
    and n in the order a frame or a call binds them. *)
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
    (en; sl; sl; sl; normt n8 ltac:(symmetry; apply neg_land7; lia); sl; sb;
     rewrite (Z.mod_small n8); [|lia]; rewrite (Z.mod_small n); [|lia];
     destruct (Z.ltb_spec n8 n) as [Hlt|Hge]; close_if;
     [en | en; sg]; sg; norm "v21" (Z.min n8 n) ltac:(arith); norm "pr.3" 0 ltac:(reflexivity);
     (iApply (byte_loop _ _ _ _ _ _ _ _ _ _ _ _ n 0 with "W1 W2 HK");
       [exact Hs1 | exact Hs2 | lia | lia | intros j Hj; lia | lia | done | lia | done | reflexivity | reflexivity])).
Qed.

(** glibc's strncmp of two strings at any shares, aliased or not, and
    any count n below 2^64: it returns [strncmp_res] n, strcmp's answer
    on the strings' first n bytes, and hands both strings back. *)
Lemma wp_glibc_strncmp_ws dq1 dq2 p1 p2 s1 s2 n Φ :
  0 <= n < 2 ^ 64 ->
  word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗
  (word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗ Φ (Ret (WInt (strncmp_res n s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strncmp [(TAtom "v0", WPtr p1); (TAtom "v2", WPtr p2); (TAtom "v4", WInt n)] [] None
             (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof. intros Hn. apply strncmp_entry; [exact Hn | left; reflexivity]. Qed.

(** A call of glibc's strncmp, in any module whose function at the
    called name g is glibc's `__GI_strncmp`, on two strings at any
    shares and a count n below 2^64: the caller resumes with
    [strncmp_res] n and both strings. *)
Lemma wp_call_glibc_strncmp f e ls l r g args rest j dq1 dq2 p1 p2 s1 s2 n cf' Φ :
  0 <= n < 2 ^ 64 ->
  map_option (arg_x ge e) args = Some [WPtr p1; WPtr p2; WInt n] -> find_fn ge g = Some (Defined glibc_strncmp) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) (Ret (WInt (strncmp_res n s1 s2))) = Some cf' ->
  word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗
  ▷ (word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hn Hx Hg Hr. iIntros "H1 H2 HK".
  iApply (wp_call_bind registry wi ge _ _ _ _ _ _ _ _ _ _ _
            (mkFrame glibc_strncmp [(TAtom "v4", WInt n); (TAtom "v2", WPtr p2); (TAtom "v0", WPtr p1)] [] None
               (Enter (TAtom "start") None))
            with "[H1 H2 HK]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply (strncmp_entry with "H1 H2"); [exact Hn | right; reflexivity |]. iIntros "H1 H2". iExists cf'. iSplit; [done|].
  iNext. iApply ("HK" with "H1 H2").
Qed.

End rules.
End StrncmpLogicOn.
