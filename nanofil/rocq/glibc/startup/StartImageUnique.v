(** A proof about startup owns many parts of a program's initial
    memory at once. It may do so only when no part is listed twice,
    because a byte of memory has one owner. The lists are long. The
    eighteen globals of `c: init_cpu_features` alone take more than
    twelve thousand entries, so a check that compares every entry with
    every other is too slow.

    This module gives a faster check. It maps each entry to a number,
    sorts the numbers, and tests that each one is smaller than the
    next. Sorting takes far fewer steps than comparing all pairs.

    The check is about lists only. It does not mention any program. *)

From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Pieces Heap.
From stdpp Require Import list sorting.
Import ListNotations.
Open Scope Z_scope.

(** ## The check *)

(** This function gives the number of an entry. Two entries of memory
    with the same number are the same entry, as long as every offset
    is below 2^40. All entries that are names get the number 3, so the
    check accepts at most one of them. *)
Definition piece_key (l : piece) : Z :=
  match l with
  | PLive b => 4 * b
  | PByte b o => 4 * (b * 2 ^ 40 + o) + 1
  | PAux b o => 4 * (b * 2 ^ 40 + o) + 2
  | PName _ => 3
  end.

(** This function tests that each number of a list is smaller than
    the one after it. *)
Fixpoint rising (ks : list Z) : bool :=
  match ks with
  | a :: (b :: _) as t => (a <? b) && rising t
  | _ => true
  end.

(** The check sorts the numbers of the entries and tests that the
    sorted list rises. *)
Definition pieces_unique (xs : list piece) : bool := rising (merge_sort Z.le (map piece_key xs)).

(** ## Why the check is right *)

(** A sorted list that rises has no number twice. *)
Lemma rising_nodup ks : StronglySorted Z.le ks -> rising ks = true -> NoDup ks.
Proof.
  induction 1 as [|a t Ht IH Ha]; [constructor|]. intros Hr. constructor.
  - intros Hin. destruct t as [|b t']; [inversion Hin|]. cbn in Hr. apply andb_prop in Hr as [Hab _].
    apply Z.ltb_lt in Hab. inversion Ht as [|? ? _ Hb]; subst.
    apply elem_of_cons in Hin as [->|Hin]; [lia|]. rewrite Forall_forall in Hb. specialize (Hb _ Hin). lia.
  - apply IH. destruct t as [|b t']; [reflexivity|]. cbn in Hr. apply andb_prop in Hr as [_ Hr]. exact Hr.
Qed.

(** A list that passes the check has no entry twice. Two equal entries
    would have equal numbers, and sorting keeps both of them. *)
Lemma pieces_unique_sound xs : pieces_unique xs = true -> NoDup xs.
Proof.
  intros H. apply (NoDup_fmap_1 piece_key). rewrite <- (merge_sort_Permutation Z.le).
  apply rising_nodup; [|exact H]. apply (StronglySorted_merge_sort Z.le).
Qed.
