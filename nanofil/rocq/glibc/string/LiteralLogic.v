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

(** The loader writes each string into its own object. This function
    lists the pieces that hold the texts ts in the objects bs, taking one
    literal after another. *)
Definition lits_ps (bs : list (Z * region)) (ts : list (list Z)) : list (piece * pval) :=
  List.concat (zip_with (fun br s => lit_ps br.1 br.2 (lit_words s)) bs ts).

(** A literal fits its object when the object starts at a positive 8-byte
    boundary and holds all its words below the top of the address space. *)
Definition lit_fit (br : Z * region) (s : list Z) : Prop :=
  0 < br.1 /\ br.1 mod 8 = 0 /\ br.1 + 8 * Z.of_nat (List.length (lit_words s)) <= r_end br.2 /\
  r_end br.2 <= 2 ^ 48.

(** ## Distinct keys

    The keys of a literal's pieces all belong to its base, so literals at
    distinct bases have disjoint keys. This proof works on the structure of
    the lists, so it never decides distinctness over all the bytes. *)

(** Every key of a literal's pieces belongs to its base. *)
Lemma lit_ps_ids b reg ws k : k ∈ (lit_ps b reg ws).*1 -> piece_id k = b.
Proof.
  cbn [lit_ps fmap list_fmap fst]. rewrite (words_ps_keys b 0 ws).
  intros [->|Hk]%elem_of_cons; [done|]. apply list_elem_of_fmap in Hk as (o & -> & _). done.
Qed.

(** Literals at distinct bases have distinct keys, and each key belongs to
    one of the bases. *)
Lemma lits_ps_keys bs ts : NoDup bs.*1 ->
  NoDup (lits_ps bs ts).*1 /\ forall k, k ∈ (lits_ps bs ts).*1 -> piece_id k ∈ bs.*1.
Proof.
  unfold lits_ps. revert ts. induction bs as [|[b reg] bs IH]; intros [|s ts] Hnd.
  - split; [constructor | intros k Hk; inversion Hk].
  - split; [constructor | intros k Hk; inversion Hk].
  - split; [constructor | intros k Hk; inversion Hk].
  - cbn [zip_with List.concat fmap list_fmap fst] in *. apply NoDup_cons in Hnd as [Hb Hnd].
    destruct (IH ts Hnd) as [IHn IHk]. rewrite fmap_app. split.
    + apply NoDup_app. split_and!; [apply lit_ps_nodup| |exact IHn].
      intros k Hk1 Hk2. apply lit_ps_ids in Hk1. apply IHk in Hk2. rewrite Hk1 in Hk2. exact (Hb Hk2).
    + intros k [Hk|Hk]%elem_of_app.
      * apply lit_ps_ids in Hk. rewrite Hk. apply elem_of_cons. by left.
      * apply elem_of_cons. right. exact (IHk k Hk).
Qed.

(** ## Keeping other pieces apart

    A caller who owns these pieces next to other startup pieces must show
    that no key repeats. The keys of a literal belong to its base, so
    other pieces only have to stay off those bases. *)

(** Pieces whose keys avoid the bases of some literals stay distinct
    from the literals' keys. *)
Lemma lits_ps_sep ps bs ts : NoDup ps.*1 -> NoDup bs.*1 ->
  (forall k, k ∈ ps.*1 -> piece_id k ∉ bs.*1) -> NoDup (ps ++ lits_ps bs ts).*1.
Proof.
  intros Hp Hb Hsep. destruct (lits_ps_keys bs ts Hb) as [Hn Hk].
  rewrite fmap_app. apply NoDup_app. split_and!; [exact Hp| |exact Hn].
  intros k Hk1 Hk2. exact (Hsep k Hk1 (Hk k Hk2)).
Qed.

Section literals.
Context `{!gen_heapGS piece pval Σ}.

(** The pieces of fitting literals with checked words freeze into their
    strings. *)
Lemma lits_own bs ts : Forall2 lit_fit bs ts -> Forall (fun s => lit_ok s = true) ts ->
  pts (lits_ps bs ts) ==∗ [∗ list] br; s ∈ bs; ts, word_string DfracDiscarded (mkPtr br.1 (Ro br.1)) s.
Proof using Type.
  unfold lits_ps. induction 1 as [|[b reg] s bs ts Hf _ IH]; intros Hok; [by iIntros "_ !>"|].
  apply Forall_cons in Hok as [Hs Hok]. destruct Hf as (H0 & H8 & He & Hr).
  cbn [zip_with List.concat]. rewrite pts_app. iIntros "[H Hs]".
  iMod (lit_own with "H") as "#H"; try assumption. iMod (IH Hok with "Hs") as "Hs".
  iModIntro. rewrite big_sepL2_cons. iFrame "H Hs".
Qed.
End literals.
