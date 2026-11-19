(** A C string literal occupies whole words in a loaded image.
    These rules turn the loader’s bytes into the shared string that a library call reads. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Values Memory Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import Fix StrlenLogic WordString LiteralWords.
Import ListNotations Fix.ML0 Fix.LG0.
Open Scope Z_scope.
Open Scope list_scope.

(** The words fit in 64 bits, their bytes spell s and a zero, and every
    character of s is a byte other than zero. *)
Definition lit_ok (s : list Z) : bool :=
  (Z.of_nat (List.length (lit_words s)) =? (Z.of_nat (List.length s) + 8) / 8) &&
  forallb (fun w => (0 <=? w) && (w <? 2 ^ 64)) (lit_words s) &&
  bool_decide (take (S (List.length s)) (wbytes (lit_words s)) = s ++ [0]) &&
  forallb (fun c => (0 <? c) && (c <? 256)) s.

(** A literal with checked words has the string shape at any read-only
    object that starts at an 8-byte boundary and holds its words. *)
Lemma lit_shape b reg s :
  0 < b -> b mod 8 = 0 -> b + 8 * Z.of_nat (List.length (lit_words s)) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  lit_ok s = true -> str_shape (mkPtr b (Ro b)) b reg (lit_words s) s.
Proof.
  intros Hb H8 Hfit Hsp Hok. unfold lit_ok in Hok. repeat rewrite andb_true_iff in Hok.
  destruct Hok as (((Hl & Hw) & Hby) & Hch). apply Z.eqb_eq in Hl.
  assert (Hst : wstart (mkPtr b (Ro b)) = b) by (unfold wstart; cbn; lia).
  split; cbn [ptr_addr ptr_cap].
  - right. reflexivity.
  - exact Hb.
  - exact H8.
  - lia.
  - rewrite Hst. exact Hfit.
  - exact Hsp.
  - rewrite H8 Z.add_0_l. exact Hl.
  - apply Forall_forall. intros w Hin. apply list_elem_of_In in Hin.
    rewrite forallb_forall in Hw. specialize (Hw w Hin). lia.
  - rewrite H8. cbn [Z.to_nat drop]. exact (bool_decide_eq_true_1 _ Hby).
  - apply Forall_forall. intros c Hin. apply list_elem_of_In in Hin.
    rewrite forallb_forall in Hch. specialize (Hch c Hin). lia.
Qed.

Section own.
Context `{!gen_heapGS piece pval Σ}.

(** The words of a checked literal make a read-only string. *)
Lemma lit_own b reg s :
  0 < b -> b mod 8 = 0 -> b + 8 * Z.of_nat (List.length (lit_words s)) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  lit_ok s = true -> pts (lit_ps b reg (lit_words s)) ==∗ word_string DfracDiscarded (mkPtr b (Ro b)) s.
Proof using Type.
  intros Hb H8 Hfit Hsp Hok. iIntros "H".
  iDestruct (word_string_literal with "H") as "H"; [exact (lit_shape b reg s Hb H8 Hfit Hsp Hok)|].
  iMod (word_string_persist with "H") as "#H". by iModIntro.
Qed.

End own.
