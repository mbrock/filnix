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
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import FileInv WordString GetoptState.
From Glibc Require FileInv GetoptState.
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


(** The state module supplies the private fields, the cursor and the session. *)
Import GetoptState FileInv FileInv.ML FileInv.LG FileInv.L.

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

End session.
