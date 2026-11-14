(** glibc's getopt keeps its scan state in a private object between
    calls, and the session predicate says what a later call may rely on.
    When the long-option parser returns, it has rewritten four of the
    object's fields: the index, the option character, the argument and
    the cursor. This file proves that the object, with the five fields
    the parser left alone, again makes up a session at the new index.
    The proof needs the bounds and the cursor that held before the call,
    and the facts that the parser's return state gives about the new
    index and the new cursor. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic StringLogic.
From Glibc Require Import FileInv WordString GetoptBytes GetoptState.
From Glibc Require FileInv GetoptBytes GetoptState.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## Bounds after a return

    The parser moves the index forward by at most two words. It moves by
    two only when a word remains for an argument, so the new index never
    passes the argument count. *)

(** After a return, the parser's four fields hold new values and the other five hold the values they had. *)
Definition long_state (s : getopt_state) (i' oo : Z) (a c : ptr) : getopt_state :=
  mkGetoptState i' (gs_err s) oo a (gs_initialized s) c (gs_order s) (gs_first s) (gs_last s).

(** A move of the index that a return allows keeps the session's bounds. *)
Lemma long_bounds n s i' oo a c :
  getopt_bounds n (gs_ind s) s -> gs_ind s < n ->
  (gs_ind s <= i' <= gs_ind s + 1 \/ (i' = gs_ind s + 2 /\ gs_ind s + 1 < n)) ->
  getopt_bounds n i' (long_state s i' oo a c).
Proof. unfold getopt_bounds, long_state. cbn. lia. Qed.

(** These controls show that the bounds need both index facts. With
    three words and the index at 1, a move by two reaches the count and
    keeps the bounds. With the index at 2, the same move passes the
    count, which the condition that a word remains rules out. *)
Lemma long_bounds_ctl_two :
  getopt_bounds 3 3 (long_state (mkGetoptState 1 1 0 null 1 null 0 1 1) 3 0 null null).
Proof. apply long_bounds; cbn; [unfold getopt_bounds; cbn; lia | lia | right; lia]. Qed.

(** A move by two from the last word would break the bounds. *)
Lemma long_bounds_ctl_past :
  ~ getopt_bounds 3 4 (long_state (mkGetoptState 2 1 0 null 1 null 0 1 1) 4 0 null null).
Proof. unfold getopt_bounds, long_state. cbn. lia. Qed.

(** A short option moves the cursor one byte into the rest of the word.
    When the rest "ab" follows the prefix "-", the step leaves the prefix
    "-a" and the rest "b", which is not empty, so the cursor still points
    inside the word. *)
Lemma short_ctl_step : take 1 [97; 98] = [97] /\ drop 1 [97; 98] = [98] /\ drop 1 [97; 98] <> [] /\
  length ([45] ++ take 1 [97; 98]) = 2%nat.
Proof. cbn. repeat split; try reflexivity; discriminate. Qed.

(** When the rest is the single byte "a", the step leaves an empty rest,
    so the cursor reaches the terminator; that is the long return's case. *)
Lemma short_ctl_last : drop 1 [97] = [].
Proof. reflexivity. Qed.

(** The step needs a rest of at least two bytes, and "a" has one. *)
Lemma short_ctl_short : ~ (1 < length [97])%nat.
Proof. cbn. lia. Qed.


(** The state module supplies the private fields, the cursor and the session. *)
Import GetoptState FileInv FileInv.ML FileInv.LG FileInv.L.
(** The byte module reads one byte of a shared string. *)

Section session.
Context `{!gen_heapGS piece pval Σ}.

(** The cursor relation depends only on the cursor and the last
    nonoption, so a state that keeps both keeps the relation. *)
Lemma long_cursor_keep ps i s s' :
  gs_next s' = gs_next s -> gs_last s' = gs_last s -> getopt_cursor ps i s -∗ getopt_cursor ps i s'.
Proof.
  intros Hn Hl. iIntros "[H | [H | H]]".
  - iLeft. by rewrite Hn.
  - iRight. iLeft. by rewrite Hn.
  - iRight. iRight. iDestruct "H" as (q prefix suffix) "[%H Hw]". iExists q, prefix, suffix.
    iFrame. iPureIntro. rewrite Hn Hl. exact H.
Qed.

(** The next call of getopt relies on the session, so every return of
    the long-option parser must leave one behind. Before the call, the
    session held at index i, and the cursor pointed into the current
    word, whose rest is t. After the return, the object holds a new
    index, option character, argument and cursor. The index moved as
    the return state allows. The cursor is null, or it stayed while the
    index stayed, or it points at the terminator at the end of the
    word. Then the object makes up a session at the new index. *)
Lemma long_session b r av ar ps s i' oo a c t :
  getopt_bounds (Z.of_nat (length ps)) (gs_ind s) s -> gs_ind s < Z.of_nat (length ps) ->
  gs_initialized s = 1 -> 0 <= gs_order s <= 2 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  (gs_ind s <= i' <= gs_ind s + 1 \/ (i' = gs_ind s + 2 /\ gs_ind s + 1 < Z.of_nat (length ps))) ->
  c = null \/ (c = gs_next s /\ i' = gs_ind s) \/ c = ptr_add (gs_next s) (Z.of_nat (length t)) ->
  getopt_cursor ps (gs_ind s) s -∗ word_string DfracDiscarded (gs_next s) t -∗
  live b r -∗ int_cell b 0 i' -∗ int_cell b 4 (gs_err s) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
  int_cell b 24 (gs_initialized s) -∗ pcell b 32 c -∗ int_cell b 40 (gs_order s) -∗
  int_cell b 44 (gs_first s) -∗ int_cell b 48 (gs_last s) -∗
  getopt_session b r av ar ps i'.
Proof.
  intros Hbd Hlt Hin Hord Hb Hal Hend Hr Hav Hala Hda Hra Hi Hc.
  iIntros "#Hcu #Hws Hl Hib Her Hoo Hab Hini Hcur Hord Hfi Hla".
  iSplit; [iPureIntro; lia|]. iExists (long_state s i' oo a c).
  iSplitL "Hl Hib Her Hoo Hab Hini Hcur Hord Hfi Hla"; [iFrame; iPureIntro; lia|].
  iSplit; [iPureIntro; by apply long_bounds|]. iRight. iSplit; [iPureIntro; cbn; lia|].
  destruct Hc as [-> | [[-> ->] | ->]].
  - by iLeft.
  - by iApply (long_cursor_keep with "Hcu").
  - iRight. iLeft. cbn. rewrite -{1}(app_nil_r t). by iApply word_string_suffix.
Qed.


(** Two shared views of strings at the same pointer hold the same byte
    at every index up to both terminators, because each view owns a
    read share of that one byte of the object. *)
Lemma short_byte_agree p s1 s2 (k : nat) : (k <= length s1)%nat -> (k <= length s2)%nat ->
  word_string DfracDiscarded p s1 -∗ word_string DfracDiscarded p s2 -∗ ⌜sbyte s1 k = sbyte s2 k⌝.
Proof.
  intros H1 H2. iIntros "W1 W2".
  iDestruct (GetoptBytes.ws_byte p s1 k H1 with "W1") as (b1 reg1) "(%Hb1 & _ & B1)".
  iDestruct (GetoptBytes.ws_byte p s2 k H2 with "W2") as (b2 reg2) "(%Hb2 & _ & B2)".
  assert (b1 = b2) as <-.
  { destruct Hb1 as [[E1|E1] _], Hb2 as [[E2|E2] _]; rewrite E1 in E2; congruence. }
  iAssert (ptsq DfracDiscarded (byte_ps b1 (ptr_addr p + Z.of_nat k - b1) [sbyte s1 k])) with "[B1]" as "B1";
    [iExact "B1"|].
  iAssert (ptsq DfracDiscarded (byte_ps b1 (ptr_addr p + Z.of_nat k - b1) [sbyte s2 k])) with "[B2]" as "B2";
    [iExact "B2"|].
  iDestruct (ptsq_agree with "B1 B2") as %E; [reflexivity|].
  rewrite !byte_ps_cons in E. by injection E.
Qed.

(** A short option reads the byte at the cursor and moves the cursor one
    byte on, at the same index, while more of the word remains. Before
    the step, the session held at index i, and the cursor pointed at the
    rest t of the current word, with at least two bytes. After the step,
    the object holds a new option character and argument and the cursor
    one byte on, and the five fields the step left alone. Then the
    object makes up a session at the same index. The session's cursor
    names the word at the index, and its prefix grows by the byte that
    the step read. *)
Lemma short_session b r av ar ps s oo a t :
  getopt_bounds (Z.of_nat (length ps)) (gs_ind s) s -> gs_ind s < Z.of_nat (length ps) ->
  gs_initialized s = 1 -> 0 <= gs_order s <= 2 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  (1 < length t)%nat ->
  getopt_cursor ps (gs_ind s) s -∗ word_string DfracDiscarded (gs_next s) t -∗
  live b r -∗ int_cell b 0 (gs_ind s) -∗ int_cell b 4 (gs_err s) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
  int_cell b 24 (gs_initialized s) -∗ pcell b 32 (ptr_add (gs_next s) 1) -∗ int_cell b 40 (gs_order s) -∗
  int_cell b 44 (gs_first s) -∗ int_cell b 48 (gs_last s) -∗
  getopt_session b r av ar ps (gs_ind s).
Proof.
  intros Hbd Hlt Hin Hord Hb Hal Hend Hr Hav Hala Hda Hra Ht.
  iIntros "Hcu #Hws Hl Hib Her Hoo Hab Hini Hcur Hord Hfi Hla".
  iDestruct (GetoptBytes.ws_shape with "Hws") as %(Htc & Hp0 & _).
  assert (Ht1 : sbyte t 1 <> 0).
  { unfold sbyte. rewrite app_nth1; [|lia]. rewrite Forall_forall in Htc.
    assert (0 < nth 1 t 0 < 256) by (apply Htc; apply nth_In; lia). lia. }
  assert (Ht0 : sbyte t 0 <> 0).
  { unfold sbyte. rewrite app_nth1; [|lia]. rewrite Forall_forall in Htc.
    assert (0 < nth 0 t 0 < 256) by (apply Htc; apply nth_In; lia). lia. }
  iSplit; [iPureIntro; lia|]. iExists (long_state s (gs_ind s) oo a (ptr_add (gs_next s) 1)).
  iSplitL "Hl Hib Her Hoo Hab Hini Hcur Hord Hfi Hla"; [iFrame; iPureIntro; lia|].
  iSplit; [iPureIntro; apply long_bounds; [exact Hbd | exact Hlt | left; lia]|].
  iRight. iSplit; [iPureIntro; cbn; lia|].
  iDestruct "Hcu" as "[%Hn | [#H0 | (%q & %prefix & %suffix & %Hc & #Hwq)]]".
  - exfalso. rewrite Hn in Hp0. cbn in Hp0. lia.
  - iDestruct (short_byte_agree _ [] t 0 with "H0 Hws") as %E; [cbn; lia | lia |].
    exfalso. apply Ht0. rewrite -E. reflexivity.
  - destruct Hc as (Hi & Hq & Hsne & Hnx & Hla').
    iAssert (word_string DfracDiscarded (gs_next s) suffix) as "#Hsf".
    { rewrite Hnx. by iApply word_string_suffix. }
    destruct suffix as [|c0 [|c1 rest]]; [done| |].
    + iDestruct (short_byte_agree _ [c0] t 1 with "Hsf Hws") as %E; [cbn; lia | lia |].
      exfalso. apply Ht1. rewrite -E. reflexivity.
    + iRight. iRight. iExists q, (prefix ++ [c0]), (c1 :: rest). iSplit.
      * iPureIntro. cbn [long_state gs_next gs_last]. split; [lia|]. split; [exact Hq|]. split; [discriminate|].
        split; [|exact Hla']. rewrite Hnx length_app. cbn [length]. unfold ptr_add. cbn. f_equal. lia.
      * by rewrite -app_assoc.
Qed.
End session.
