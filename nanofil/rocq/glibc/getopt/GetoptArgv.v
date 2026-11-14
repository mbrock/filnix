(** Glibc's option scanner permutes the caller's argument vector in
    place, so that options come before the arguments they skipped. The
    caller therefore lends the scanner every pointer cell of the vector.
    This file states that ownership as one stored pointer per argument and
    shows that exchanging two cells keeps it. An exchange only reorders
    the caller's pointers, so the vector stays a permutation of the
    original arguments. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## Exchanging two entries *)

(** Exchanging entries j and k writes each one's pointer into the other. *)
Definition swap_at (ps : list ptr) (j k : nat) : list ptr :=
  <[k := nth j ps null]> (<[j := nth k ps null]> ps).

(** Overwriting an entry before removing it removes the original entry. *)
Lemma delete_insert_same (l : list ptr) i x : delete i (<[i := x]> l) = delete i l.
Proof. revert i. induction l as [|y l IH]; intros [|i]; cbn; f_equal; auto. Qed.

(** An overwritten entry moves to the front up to permutation. *)
Lemma insert_perm (l : list ptr) i x : (i < length l)%nat -> Permutation (<[i := x]> l) (x :: delete i l).
Proof.
  intros Hi. rewrite -(delete_insert_same l i x). apply delete_Permutation.
  by apply list_lookup_insert_eq.
Qed.

(** An exchange keeps the length of the vector. *)
Lemma length_swap_at ps j k : length (swap_at ps j k) = length ps.
Proof. unfold swap_at. by rewrite !length_insert. Qed.

(** An exchange of two entries in range only reorders the vector. *)
Lemma swap_at_perm ps j k : (j < length ps)%nat -> (k < length ps)%nat -> Permutation ps (swap_at ps j k).
Proof.
  intros Hj Hk. unfold swap_at.
  destruct (lookup_lt_is_Some_2 ps j Hj) as [x Hx].
  destruct (lookup_lt_is_Some_2 ps k Hk) as [y Hy].
  rewrite (nth_lookup_Some _ _ _ _ Hx) (nth_lookup_Some _ _ _ _ Hy).
  set (L1 := <[j := y]> ps).
  assert (H1 : (k < length L1)%nat) by (unfold L1; by rewrite length_insert).
  assert (HL1 : L1 !! k = Some y).
  { unfold L1. destruct (decide (k = j)) as [->|Hne]; [by apply list_lookup_insert_eq|].
    rewrite list_lookup_insert_ne; [done|]. congruence. }
  assert (Hd : Permutation (delete j ps) (delete k L1)).
  { apply Permutation_cons_inv with (a := y).
    rewrite -(insert_perm ps j y Hj) -/L1. by apply delete_Permutation. }
  rewrite (insert_perm L1 k x H1) -Hd. by apply delete_Permutation.
Qed.

(** The scanner owns every argument pointer cell of the vector it permutes. *)
Import LG0 LG0.L.

Section argv.
Context `{!gen_heapGS piece pval Σ}.

(** The vector object av holds pointer ps[k] at offset 8k. *)
Definition argv_cells (av : Z) (ps : list ptr) : iProp Σ :=
  [∗ list] k ↦ q ∈ ps, pcell av (8 * Z.of_nat k) q.

(** Two distinct cells come out of the vector together. Writing any two
    pointers back yields the vector with those entries replaced. *)
Lemma argv_cells_two av ps j k : j <> k -> (j < length ps)%nat -> (k < length ps)%nat ->
  argv_cells av ps -∗
  pcell av (8 * Z.of_nat j) (nth j ps null) ∗ pcell av (8 * Z.of_nat k) (nth k ps null) ∗
  (∀ a b, pcell av (8 * Z.of_nat j) a -∗ pcell av (8 * Z.of_nat k) b -∗
     argv_cells av (<[k := b]> (<[j := a]> ps))).
Proof.
  intros Hne Hj Hk. iIntros "H".
  destruct (lookup_lt_is_Some_2 ps j Hj) as [x Hx].
  destruct (lookup_lt_is_Some_2 ps k Hk) as [y Hy].
  rewrite (nth_lookup_Some _ _ _ _ Hx) (nth_lookup_Some _ _ _ _ Hy).
  set (Ψ := fun i q => (if decide (i = k) then emp else pcell av (8 * Z.of_nat i) q)%I).
  iEval (unfold argv_cells; rewrite (big_sepL_delete _ ps k y Hy)) in "H".
  iDestruct "H" as "[Hy H]". fold (Ψ : nat -> ptr -> iProp Σ).
  iDestruct (big_sepL_insert_acc Ψ ps j x Hx with "H") as "[Hx Hj]".
  unfold Ψ at 1. rewrite decide_False; [|done]. iFrame "Hx Hy". iIntros (a b) "Ha Hb".
  iSpecialize ("Hj" $! a with "[Ha]"); [unfold Ψ; by rewrite decide_False|].
  assert (HL : <[j := a]> ps !! k = Some y) by (rewrite list_lookup_insert_ne; [done|congruence]).
  iDestruct (big_sepL_insert_acc Ψ _ k y HL with "Hj") as "[_ Hk]".
  iSpecialize ("Hk" $! b with "[]"); [unfold Ψ; by rewrite decide_True|].
  assert (HL2 : <[k := b]> (<[j := a]> ps) !! k = Some b) by (apply list_lookup_insert_eq; by rewrite length_insert).
  unfold argv_cells. iEval (rewrite (big_sepL_delete (fun i q => pcell av (8 * Z.of_nat i) q) _ k b HL2)).
  iFrame "Hb". iExact "Hk".
Qed.

End argv.
