(** In C, `c: strncmp` behaves like `c: strcmp` except that it compares
    at most n bytes and returns zero if the strings match up to that
    limit. Truncating both strings to their first n bytes reduces the
    byte-level specification of `c: strncmp` directly to [strcmp_res]
    ([StrcmpBits](StrcmpBits.v)).

    The word loops in `c: strncmp` also need a boundary check on exit:
    if a mismatch or NUL occurs at byte j inside the final 64-bit word,
    the function must still return zero whenever the remaining byte
    count r runs out at or before j. This module defines [strncmp_res]
    and proves the bounded exit lemmas for that final word
    comparison. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia List Bool.
From Nanofil Require Import Syntax Values Memory Ops.
From Glibc Require Import StrlenBits StrlenLogic WordString StrcmpBits.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The answer on byte lists

    We specify `c: strncmp` on two strings s1 and s2 with limit n by
    taking the first n bytes of each list and calling [strcmp_res]. To
    reuse the byte-function lemmas from [StrcmpBits](StrcmpBits.v),
    [cut] zeroes out any byte function from index n onward, which lets
    [strncmp_stop] and [strncmp_same] read the result from any functions
    that agree with the strings. *)

(** Function [strncmp_res] computes the `c: strncmp` return value for
    strings s1 and s2 with limit n by calling [strcmp_res] on their
    first n bytes. *)
Definition strncmp_res (n : Z) (s1 s2 : list Z) : Z :=
  strcmp_res (take (Z.to_nat n) s1) (take (Z.to_nat n) s2).

(** Function [cut] truncates a byte function f at index n by returning
    f j for j < n and 0 from index n onward. *)
Definition cut (n : Z) (f : Z -> Z) (j : Z) : Z := if j <? n then f j else 0.

(** Whenever f agrees with string s through its NUL terminator, [cut] n f
    agrees with the first n bytes of s. *)
Lemma agree_cut f s n : 0 <= n -> agree_str f s -> agree_str (cut n f) (take (Z.to_nat n) s).
Proof.
  intros Hn A j Hj. rewrite length_take in Hj. unfold cut. destruct (Z.ltb_spec j n) as [Hjn|Hjn].
  - rewrite A; [|lia]. destruct (Nat.lt_ge_cases (Z.to_nat j) (length s)) as [H|H].
    + rewrite -{1}(take_drop (Z.to_nat n) s) -app_assoc.
      rewrite !app_nth1; [reflexivity | rewrite length_take; lia | rewrite length_take; lia].
    + rewrite take_ge; [reflexivity | lia].
  - assert (E : Z.to_nat j = length (take (Z.to_nat n) s)) by (rewrite length_take; lia).
    rewrite E app_nth2; [|lia]. rewrite Nat.sub_diag. reflexivity.
Qed.

(** When f1 and f2 agree with strings s1 and s2 and first stop at index
    i below n, [strncmp_res] equals their byte difference at i modulo
    2^32. *)
Lemma strncmp_stop s1 s2 f1 f2 n i :
  Forall (fun c => 0 < c < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> 0 <= i < n ->
  same_upto f1 f2 i -> stop_at f1 f2 i -> strncmp_res n s1 s2 = (f1 i - f2 i) mod 2 ^ 32.
Proof.
  intros Hc A1 A2 Hi Hs Hst. unfold strncmp_res.
  rewrite (strcmp_res_stop _ _ (cut n f1) (cut n f2) i); [ | | apply agree_cut; [lia | exact A1]
    | apply agree_cut; [lia | exact A2] | lia | | ].
  - unfold cut. replace (i <? n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - apply Forall_take. eapply Forall_impl; [|exact Hc]. cbn. intros; lia.
  - intros j Hj. unfold cut. replace (j <? n) with true by (symmetry; apply Z.ltb_lt; lia). apply Hs, Hj.
  - unfold stop_at, cut. replace (i <? n) with true by (symmetry; apply Z.ltb_lt; lia). exact Hst.
Qed.

(** When f1 and f2 agree with strings s1 and s2 and have no stop below
    n, [strncmp_res] returns 0. *)
Lemma strncmp_same s1 s2 f1 f2 n :
  Forall (fun c => 0 < c < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> 0 <= n ->
  same_upto f1 f2 n -> strncmp_res n s1 s2 = 0.
Proof.
  intros Hc A1 A2 Hn Hs. unfold strncmp_res.
  rewrite (strcmp_res_stop _ _ (cut n f1) (cut n f2) n); [ | | apply agree_cut; [lia | exact A1]
    | apply agree_cut; [lia | exact A2] | lia | | ].
  - unfold cut. rewrite Z.ltb_irrefl. reflexivity.
  - apply Forall_take. eapply Forall_impl; [|exact Hc]. cbn. intros; lia.
  - intros j Hj. unfold cut. replace (j <? n) with true by (symmetry; apply Z.ltb_lt; lia). apply Hs, Hj.
  - left. unfold cut. rewrite Z.ltb_irrefl. reflexivity.
Qed.

(** ## The last comparison of two words

    When a word loop exits—either because a word pair stops early or
    because at most eight bytes remain—glibc compares the last pair of
    words x and y against the remaining byte count r. The predicate
    [last_cmp] captures the exact invariants at that exit, and
    [fin_stop] and [fin_none] compute the resulting [strncmp_res] value
    depending on whether x and y stop before r expires. *)

(** Every pair of 64-bit words x and y either has a first stopping byte
    j below 8 or agrees on all eight nonzero bytes. *)
Lemma word_first_stop x y :
  (exists j, 0 <= j < 8 /\ stop_at (byte_of x) (byte_of y) j /\ same_upto (byte_of x) (byte_of y) j) \/
  same_upto (byte_of x) (byte_of y) 8.
Proof.
  destruct (idx_dec (fun j => byte_of x j = byte_of y j /\ byte_of x j <> 0)
              (fun j => decide (byte_of x j = byte_of y j /\ byte_of x j <> 0)) 8) as [H|(u & Hu & Hn)].
  - right. intros j Hj. apply H. cbn. lia.
  - left. assert (Hst : stop_at (byte_of x) (byte_of y) u).
    { unfold stop_at. destruct (Z.eq_dec (byte_of x u) 0); [left; done|]. right. intros E. apply Hn. auto. }
    destruct (first_stop _ _ 0 u ltac:(cbn in Hu; lia) Hst ltac:(intros j Hj; lia)) as (j & Hj & Hsj & Hs).
    exists j. split; [cbn in Hu; lia|]. auto.
Qed.

(** When words x and y match on all eight nonzero bytes, [cmp_mask] x y
    equals 0. *)
Lemma cmp_mask_none x y : same_upto (byte_of x) (byte_of y) 8 -> cmp_mask x y = 0.
Proof.
  intros Hs. apply zero_word; [apply cmp_mask_range|]. intros i Hi. rewrite cmp_mask_byte; [|exact Hi].
  destruct (Hs i Hi) as [E N]. rewrite (proj2 (Z.eqb_neq _ _) N) E Z.eqb_refl. reflexivity.
Qed.

(** Predicate [last_cmp] records that f1 and f2 match before c, match x
    and y for L bytes from c, and either exhaust the remaining count r
    within L bytes or stop inside L. *)
Definition last_cmp (f1 f2 : Z -> Z) (c x y L r : Z) : Prop :=
  0 <= c /\ same_upto f1 f2 c /\ 0 <= L <= 8 /\ 0 < r /\
  (forall u, 0 <= u < L -> f1 (c + u) = byte_of x u /\ f2 (c + u) = byte_of y u) /\
  (r <= L \/ exists u, 0 <= u < L /\ stop_at (byte_of x) (byte_of y) u).

(** Every byte that the remaining count reaches before the first stop of
    x and y falls inside the L compared bytes. *)
Lemma last_cmp_below f1 f2 c x y L r j : last_cmp f1 f2 c x y L r -> same_upto (byte_of x) (byte_of y) j ->
  forall u, 0 <= u < Z.min r j -> u < L.
Proof.
  intros (_ & _ & _ & _ & _ & [Hr | (u' & Hu' & Hst)]) Hs u Hu; [lia|].
  destruct (Z.lt_ge_cases u' j) as [Hlt|Hge]; [|lia].
  exfalso. destruct (Hs u' ltac:(lia)) as [E N]. destruct Hst; contradiction.
Qed.

(** When x and y first stop at byte j, [fin_stop] returns 0 if the
    remaining count r is at most j, and the byte difference at j
    otherwise. *)
Lemma fin_stop s1 s2 f1 f2 c x y L r j :
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> last_cmp f1 f2 c x y L r ->
  0 <= j < 8 -> stop_at (byte_of x) (byte_of y) j -> same_upto (byte_of x) (byte_of y) j ->
  strncmp_res (c + r) s1 s2 = if r <=? j then 0 else (byte_of x j - byte_of y j) mod 2 ^ 32.
Proof.
  intros Hc A1 A2 Hl Hj Hst Hs. pose proof (last_cmp_below _ _ _ _ _ _ _ _ Hl Hs) as HL.
  destruct Hl as (H0 & Hsc & HL8 & Hr & Hb & Hor).
  assert (Hsame : forall k, 0 <= k <= Z.min r j -> same_upto f1 f2 (c + k)).
  { intros k Hk i Hi. destruct (Z.lt_ge_cases i c); [apply Hsc; lia|].
    destruct (Hb (i - c) ltac:(specialize (HL (i - c)); lia)) as [F1 F2].
    replace (c + (i - c)) with i in F1, F2 by lia. rewrite F1 F2. apply Hs. lia. }
  destruct (Z.leb_spec r j) as [Hrj|Hrj].
  - apply (strncmp_same _ _ f1 f2); [exact Hc | exact A1 | exact A2 | lia | apply Hsame; lia].
  - assert (HjL : j < L).
    { destruct Hor as [HrL | (u' & Hu' & Hst')]; [lia|].
      destruct (Z.lt_ge_cases u' j) as [Hlt|]; [|lia]. exfalso. destruct (Hs u' ltac:(lia)) as [E N].
      destruct Hst'; contradiction. }
    destruct (Hb j ltac:(lia)) as [F1 F2].
    rewrite (strncmp_stop _ _ f1 f2 (c + r) (c + j) Hc A1 A2 ltac:(lia) ltac:(apply Hsame; lia)).
    + rewrite F1 F2. reflexivity.
    + unfold stop_at. rewrite F1 F2. exact Hst.
Qed.

(** When words x and y have no zero or differing byte, the remaining
    count ends within eight bytes and the answer is 0. *)
Lemma fin_none s1 s2 f1 f2 c x y L r :
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> last_cmp f1 f2 c x y L r ->
  same_upto (byte_of x) (byte_of y) 8 -> r <= 8 /\ strncmp_res (c + r) s1 s2 = 0.
Proof.
  intros Hc A1 A2 Hl Hs.
  assert (Hr8 : r <= 8).
  { destruct Hl as (_ & _ & HL8 & _ & _ & [HrL | (u' & Hu' & Hst)]); [lia|].
    exfalso. destruct (Hs u' ltac:(lia)) as [E N]. destruct Hst; contradiction. }
  split; [exact Hr8|].
  pose proof (last_cmp_below _ _ _ _ _ _ _ _ Hl Hs) as HL. destruct Hl as (H0 & Hsc & HL8 & Hr & Hb & _).
  apply (strncmp_same _ _ f1 f2); [exact Hc | exact A1 | exact A2 | lia|].
  intros i Hi. destruct (Z.lt_ge_cases i c); [apply Hsc; lia|].
  destruct (Hb (i - c) ltac:(specialize (HL (i - c)); lia)) as [F1 F2].
  replace (c + (i - c)) with i in F1, F2 by lia. rewrite F1 F2. apply Hs. lia.
Qed.

(** When both strings match word x from offset c, x contains a zero byte,
    and more than eight bytes remain, [strncmp_res] returns 0. *)
Lemma word_zero_n s1 s2 f1 f2 c x r :
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> 0 <= c -> same_upto f1 f2 c ->
  0 <= x < 2 ^ 64 -> (forall u, 0 <= u < 8 -> f1 (c + u) = byte_of x u /\ f2 (c + u) = byte_of x u) ->
  loop_mask x <> 0 -> 8 < r -> strncmp_res (c + r) s1 s2 = 0.
Proof.
  intros Hc A1 A2 H0 Hs Hx Hb Hm Hr. destruct (loop_mask_has_zero x Hx Hm) as (u & Hu & Hz).
  assert (Hl : last_cmp f1 f2 c x x 8 r).
  { split; [lia|]. split; [exact Hs|]. split; [lia|]. split; [lia|]. split; [exact Hb|].
    right. exists u. split; [exact Hu | left; exact Hz]. }
  destruct (word_first_stop x x) as [(j & Hj & Hst & Hsj) | Hsj].
  - rewrite (fin_stop _ _ _ _ _ _ _ _ _ j Hc A1 A2 Hl Hj Hst Hsj).
    replace (r <=? j) with false by (symmetry; apply Z.leb_gt; lia). rewrite Z.sub_diag. reflexivity.
  - exfalso. destruct (Hsj u Hu) as [_ N]. contradiction.
Qed.
