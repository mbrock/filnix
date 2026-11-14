(** When glibc's scanner finds an argument that starts with a dash and
    has a second character, it hands that argument to the code that
    chooses between a long option and a group of short options. The
    proof of the scanner and the proof of the choice were written
    separately, and their interfaces state the same facts in different
    shapes. This file shows that what the scanner leaves at that exit,
    together with what the setup blocks computed before the scan, meets
    the premises of the choice. The argument count bound is the one
    exception: the choice needs a bound one smaller than the scanner's,
    and the caller must supply it. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import FileInv WordString GetoptState GetoptInitialize GetoptExchange GetoptReturn
  GetoptIdlePath GetoptScanEnd GetoptEntry GetoptEntryScan.
Import ListNotations.
Open Scope Z_scope.

(** ## Names the choice reads

    The choice reads values that earlier blocks stored under names in
    the environment. If the scan overwrote one of them, the choice would
    read a wrong value. The scan leaves the setup's values alone, and it
    stores one checked pointer of its own that the choice also reads. *)

(** These are the names that the choice keeps, in the order of its own list. *)
Definition scan_choice_keys : list name := List.map TAtom
  ["v0"; "v2"; "pr.1"; "v6"; "v8"; "v10"; "v12"; "pr.3"; "v80"; "chk2"; "chk20"]%string.

(** Every name that the choice keeps is one that the setup's
    environment fact reads, so a scan that keeps the setup's names also
    keeps the choice's. *)
Lemma scan_choice_keys_incl : incl scan_choice_keys entry_scan_keys.
Proof.
  unfold incl, scan_choice_keys, entry_scan_keys. cbn [List.map In].
  intros k Hk. intuition (subst; auto 20).
Qed.

(** The setup's names do not include chk100, so a caller cannot carry
    an older value of it across the scan. The value must come from the
    scanner's exit. *)
Lemma scan_choice_ctl_chk100 : ~ In (TAtom "chk100") entry_scan_keys.
Proof. unfold entry_scan_keys. cbn [List.map In]. intuition discriminate. Qed.

(** Before it reads the argument, the choice looks up the count, the
    vector, the option string, the long-option table and the index cell,
    with a few flags and checked pointers. The setup computed all but
    one of them, and the scanner computed the last checked pointer. *)
Lemma scan_choice_env e n av p lo li lonly b pe :
  entry_env e n (mkPtr av (Obj av)) p lo li lonly b pe ->
  lookup (TAtom "chk100") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v0") e = Some (WInt n) /\ lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) /\
  lookup (TAtom "pr.1") e = Some (WPtr p) /\ lookup (TAtom "v6") e = Some (WPtr lo) /\
  lookup (TAtom "v8") e = Some (WPtr li) /\ lookup (TAtom "v10") e = Some (WInt lonly) /\
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) /\ lookup (TAtom "pr.3") e = Some (WInt pe) /\
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) /\
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
  lookup (TAtom "chk100") e = Some (WPtr (mkPtr b (Obj b))).
Proof. unfold entry_env. tauto. Qed.

(** ## Numbers and the argument after the scan

    The scanner may permute the argument vector, so the choice must
    read the argument from the permuted vector at the new index. These
    lemmas carry the length across the permutation, find the argument,
    and pass on the bounds that the choice needs. *)

(** The scan may move words around, and the choice then reads the word
    at the new index. A permutation keeps the length, so that index is
    still below the count. The word found there is the one that the
    scanner returned. The caller's count bound and the bound past the
    final null pointer pass through unchanged. *)
Lemma scan_choice_nums (ps ps' : list ptr) n i i' f' l' av ar :
  Permutation ps ps' -> Z.of_nat (List.length ps) = n -> 0 <= f' <= l' -> l' <= i' -> 0 <= i <= i' -> i' < n ->
  n < 2 ^ 31 - 1 -> av + 8 * (n + 1) <= r_end ar ->
  Z.of_nat (List.length ps') = n /\ 0 <= i' < n /\ n < 2 ^ 31 - 1 /\
  ps' !! Z.to_nat i' = Some (nth (Z.to_nat i') ps' null) /\ 0 <= f' <= l' /\ l' <= i' /\
  av + 8 * (n + 1) <= r_end ar.
Proof.
  intros Hp Hlen Hfl Hli Hi Hin Hn Hav.
  assert (Hlen' : Z.of_nat (List.length ps') = n) by (rewrite -(Permutation_length Hp); exact Hlen).
  destruct (lookup_lt_is_Some_2 ps' (Z.to_nat i')) as [q Hq]; [lia|].
  rewrite (nth_lookup_Some _ _ _ _ Hq). repeat split; first [exact Hq | lia].
Qed.

(** The scanner allows a count of 2147483647, but the choice does not,
    because it may move the index past the current word. The bridge
    therefore takes the choice's bound as a premise. *)
Lemma scan_choice_ctl_bound : 2147483647 < 2 ^ 31 /\ ~ (2147483647 < 2 ^ 31 - 1).
Proof. lia. Qed.

(** After a permutation that swaps the first two words, the word at
    index 1 is the old first word. Reading the old vector at the same
    index would give a different word, so the argument must come from
    the permuted vector. *)
Lemma scan_choice_ctl_permuted :
  Permutation [mkPtr 8 CNone; mkPtr 16 CNone; mkPtr 24 CNone] [mkPtr 16 CNone; mkPtr 8 CNone; mkPtr 24 CNone] /\
  nth 1 [mkPtr 16 CNone; mkPtr 8 CNone; mkPtr 24 CNone] null = mkPtr 8 CNone /\
  nth 1 [mkPtr 8 CNone; mkPtr 16 CNone; mkPtr 24 CNone] null <> mkPtr 8 CNone.
Proof. split; [apply perm_swap | split; [reflexivity | discriminate]]. Qed.

(** The choice needs the waiting block at or below the index. The
    scanner's exit gives that order, and a block that ended after the
    index would break it. *)
Lemma scan_choice_ctl_order : ~ (0 <= 1 <= 3 /\ 3 <= 2).
Proof. lia. Qed.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptScanChoiceOn (R : Runtime) (LG0 : LogicSig R).
(** The bridge module carries the setup's environment fact across the scan. *)
Module ES := GetoptEntryScanOn R LG0.
Import ES.X ES.X.I ES.X.I.S ES.X.I.S.FI ES.X.I.S.FI.ML ES.X.I.S.FI.LG ES.X.I.S.FI.L ES.X.A.

(** After the scan, the choice can look up every value it needs. The
    scan kept the setup's values, and the caller takes chk100 from the
    scan's own exit. *)
Lemma scan_choice_env_keeps ks e e' n av p lo li lonly b pe :
  keeps ks e e' -> incl entry_scan_keys ks -> entry_env e n (mkPtr av (Obj av)) p lo li lonly b pe ->
  lookup (TAtom "chk100") e' = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v0") e' = Some (WInt n) /\ lookup (TAtom "v2") e' = Some (WPtr (mkPtr av (Obj av))) /\
  lookup (TAtom "pr.1") e' = Some (WPtr p) /\ lookup (TAtom "v6") e' = Some (WPtr lo) /\
  lookup (TAtom "v8") e' = Some (WPtr li) /\ lookup (TAtom "v10") e' = Some (WInt lonly) /\
  lookup (TAtom "v12") e' = Some (WPtr (mkPtr b (Obj b))) /\ lookup (TAtom "pr.3") e' = Some (WInt pe) /\
  lookup (TAtom "chk2") e' = Some (WPtr (mkPtr b (Obj b))) /\
  lookup (TAtom "chk20") e' = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
  lookup (TAtom "chk100") e' = Some (WPtr (mkPtr b (Obj b))).
Proof.
  intros Hk Hin Henv H100. apply scan_choice_env; [|exact H100].
  exact (ES.entry_env_keeps ks e e' n _ p lo li lonly b pe Hk Hin Henv).
Qed.

Section scan_choice.
Context `{!gen_heapGS piece pval Σ}.

(** The scanner's option exit hands back six fields of the private
    object, the permuted vector and the word at the new index, and the
    caller still holds the four fields that the scanner never touched.
    The choice wants all nine fields together and the word under the
    name of the vector's entry. This lemma assembles them in the choice's
    order and names the entry. *)
Lemma scan_choice_cells b r av ar (ps' : list ptr) i' s a o f' l' err oo c :
  (Z.to_nat i' < List.length ps')%nat ->
  word_string DfracDiscarded (nth (Z.to_nat i') ps' null) s -∗
  live b r -∗ int_cell b 0 i' -∗ pcell b 16 a -∗ int_cell b 40 o -∗ int_cell b 44 f' -∗ int_cell b 48 l' -∗
  int_cell b 4 err -∗ int_cell b 8 oo -∗ int_cell b 24 1 -∗ pcell b 32 c -∗
  live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
  ∃ q, ⌜ps' !! Z.to_nat i' = Some q⌝ ∗ word_string DfracDiscarded q s ∗
    live b r ∗ int_cell b 0 i' ∗ int_cell b 4 err ∗ int_cell b 8 oo ∗ pcell b 16 a ∗ int_cell b 24 1 ∗
    pcell b 32 c ∗ int_cell b 40 o ∗ int_cell b 44 f' ∗ int_cell b 48 l' ∗
    live av ar ∗ argv_cells av ps' ∗ argv_strs ps'.
Proof.
  intros Hi. destruct (lookup_lt_is_Some_2 ps' (Z.to_nat i') Hi) as [q Hq].
  iIntros "Hw Hl Hi Ha Ho Hf Hla He Hoo Hin Hc Hva Hvc Hvs".
  rewrite (nth_lookup_Some _ _ _ _ Hq). iExists q. by iFrame.
Qed.

End scan_choice.
End GetoptScanChoiceOn.
