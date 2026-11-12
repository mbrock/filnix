(** Printf-buffer completion checks whether an unsigned accumulated count fits
    a nonnegative C int. Its checked body tests both the narrowed result and
    the carry from the 64-bit addition. The carry test matters when a large
    count wraps to a small value.

    These arithmetic facts support the instruction proof of completion.
    They do not establish that a formatter produces any particular count. *)
From Stdlib Require Import ZArith Bool Lia.
From Nanofil Require Import Ops Interval.
Open Scope Z_scope.

(** The two comparisons detect narrowing loss and disagreement with the addition carry. *)
Definition printf_count_overflow (written used : Z) : bool :=
  let total := (written + used) mod 2 ^ 64 in
  let narrowed := sign_extension (2 ^ 32) (2 ^ 31) total in
  negb (total =? narrowed mod 2 ^ 64) ||
  negb ((if total <? written then 1 else 0) =? (narrowed / 2 ^ 63) mod 2 ^ 64).

(** A signed C int survives extension through a 64-bit register unchanged. *)
Lemma printf_signed64_int n : - 2 ^ 31 <= n < 2 ^ 31 ->
  sign_extension (2 ^ 64) (2 ^ 63) (n mod 2 ^ 64) = n.
Proof.
  intros Hn. unfold sign_extension. rewrite Z.mod_mod by lia.
  destruct (Z_lt_le_dec n 0).
  - replace (n mod 2 ^ 64) with (n + 2 ^ 64).
    + rewrite (proj2 (Z.leb_le _ _)) by lia. lia.
    + apply Z.mod_unique with (-1); lia.
  - rewrite Z.mod_small by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.

(** Passing both tests means the mathematical sum fits, even when unsigned addition could wrap. *)
Lemma printf_count_fits written used :
  0 <= written < 2 ^ 64 -> 0 <= used < 2 ^ 64 ->
  printf_count_overflow written used = false <-> written + used < 2 ^ 31.
Proof.
  intros Hw Hu. unfold printf_count_overflow.
  set (total := (written + used) mod 2 ^ 64).
  set (narrowed := sign_extension (2 ^ 32) (2 ^ 31) total).
  assert (Htotal : 0 <= total < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (Hn : - 2 ^ 31 <= narrowed < 2 ^ 31).
  { apply sign_extension_range; lia. }
  split.
  - intros H. apply orb_false_iff in H as [He Hcarry].
    apply negb_false_iff in He. apply Z.eqb_eq in He.
    apply negb_false_iff in Hcarry. apply Z.eqb_eq in Hcarry.
    assert (Hnonnegative : 0 <= narrowed).
    { destruct (Z_lt_le_dec narrowed 0); [|assumption].
      assert (Hdiv : narrowed / 2 ^ 63 = -1).
      { symmetry. apply Z.div_unique with (r := narrowed + 2 ^ 63); lia. }
      rewrite Hdiv in Hcarry.
      change ((if total <? written then 1 else 0) = 18446744073709551615) in Hcarry.
      destruct (total <? written); lia. }
    rewrite Z.div_small in Hcarry by lia.
    change ((if total <? written then 1 else 0) = 0) in Hcarry.
    assert (Hnocarry : written <= total).
    { destruct (total <? written) eqn:E; [discriminate|now apply Z.ltb_ge in E]. }
    assert (Hsum : written + used < 2 ^ 64).
    { destruct (Z_lt_le_dec (written + used) (2 ^ 64)); [assumption|].
      assert (Hwrap : total = written + used - 2 ^ 64).
      { unfold total. symmetry. apply Z.mod_unique with 1; lia. }
      lia. }
    unfold total in He. rewrite Z.mod_small in He by lia.
    rewrite Z.mod_small in He by lia. lia.
  - intros Hsum.
    assert (Ht : total = written + used) by (unfold total; apply Z.mod_small; lia).
    assert (Hnarrow : narrowed = total).
    { unfold narrowed, sign_extension. rewrite Z.mod_small by lia.
      rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
    rewrite Hnarrow. rewrite Z.mod_small by lia. rewrite Z.eqb_refl.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    rewrite Z.div_small by lia. reflexivity.
Qed.

(** Every canonical unsigned sum outside the C int range takes the overflow branch. *)
Lemma printf_count_overflows written used :
  0 <= written < 2 ^ 64 -> 0 <= used < 2 ^ 64 ->
  2 ^ 31 <= written + used -> printf_count_overflow written used = true.
Proof.
  intros Hw Hu Hsum. destruct (printf_count_overflow written used) eqn:E; [reflexivity|].
  apply (proj1 (printf_count_fits written used Hw Hu)) in E. lia.
Qed.
