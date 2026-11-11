(** The byte and bit facts glibc's word-at-a-time `strcmp`
    (StrcmpCode.v) rests on, for StrcmpLogic.v's triple over
    [word_string]s (WordString.v).

    - [strcmp_res] is the answer on byte lists: 0 for equal strings,
      else the difference of the first bytes of s1 and s2, each with its
      NUL, that differ, as glibc computes it in a 32-bit `int`;
      [strcmp_res_zero] says it is 0 exactly for equal strings.
    - [strcmp_res_stop] reads it off any two byte functions that agree
      with the strings through their NULs, at the first index where the
      first is 0 or they differ: every return of strcmp is such a stop.
    - [bt] ws i is byte i of the words ws, so a string's bytes from p are
      [bt] from p's offset in its word ([str_bt]).
    - [cmp_mask] is the mask glibc's `find_zero_ne_all` (string-fzc.h)
      makes of two words, as nanofil's IR computes it: 128 in each byte
      where the first word's is 0 or the two differ ([cmp_mask_byte]),
      and its population count finds the first such byte
      ([cmp_mask_first]).
    - [merge] is glibc's `MERGE` of two words for an unaligned second
      string: its bytes are the words' bytes from an offset
      ([merge_byte], [bt_merge]).
    - [loop_mask] (StrlenBits.v), glibc's `has_zero`, is 0 exactly for
      a word with no zero byte ([loop_mask_zero]). *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia List Bool.
From Nanofil Require Import Syntax Values Memory Ops.
From Glibc Require Import StrlenBits StrlenLogic WordString.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The answer on byte lists *)

(** strcmp's answer for the strings s1 and s2, without their NULs: the
    difference, modulo 2^32, of the first bytes of s1 ++ [0] and
    s2 ++ [0] that differ, or 0 if none do. *)
Fixpoint strcmp_res (s1 s2 : list Z) : Z :=
  match s1, s2 with
  | [], [] => 0
  | c1 :: s1', c2 :: s2' => if c1 =? c2 then strcmp_res s1' s2' else (c1 - c2) mod 2 ^ 32
  | [], c2 :: _ => (0 - c2) mod 2 ^ 32
  | c1 :: _, [] => (c1 - 0) mod 2 ^ 32
  end.

(** A difference of two bytes, not 0, is not 0 modulo 2^32. *)
Lemma byte_diff_nonzero c1 c2 : 0 <= c1 < 256 -> 0 <= c2 < 256 -> c1 <> c2 -> (c1 - c2) mod 2 ^ 32 <> 0.
Proof. intros H1 H2 Hne E. apply Z.mod_divide in E; [|lia]. destruct E as [k Hk]. nia. Qed.

(** For strings of nonzero bytes, the answer is 0 exactly when the
    strings are equal. *)
Lemma strcmp_res_zero s1 s2 :
  Forall (fun c => 0 < c < 256) s1 -> Forall (fun c => 0 < c < 256) s2 -> (strcmp_res s1 s2 = 0 <-> s1 = s2).
Proof.
  revert s2. induction s1 as [|c1 s1 IH]; intros [|c2 s2] H1 H2; cbn [strcmp_res].
  - tauto.
  - apply Forall_cons_1 in H2 as [Hc _]. split; [|discriminate]. intros E.
    exfalso. apply (byte_diff_nonzero 0 c2); lia.
  - apply Forall_cons_1 in H1 as [Hc _]. split; [|discriminate]. intros E.
    exfalso. apply (byte_diff_nonzero c1 0); lia.
  - apply Forall_cons_1 in H1 as [Hc1 H1], H2 as [Hc2 H2]. destruct (Z.eqb_spec c1 c2) as [<-|Hne].
    + rewrite IH; [|exact H1|exact H2]. split; [intros ->; reflexivity | intros E; injection E as E; exact E].
    + split; [intros E; exfalso; exact (byte_diff_nonzero c1 c2 ltac:(lia) ltac:(lia) Hne E)|].
      intros E. injection E as E _. contradiction.
Qed.

(** The functions f1 and f2 agree with the strings s1 and s2 through
    their NULs. *)
Definition agree_str (f : Z -> Z) (s : list Z) : Prop :=
  forall j, 0 <= j <= Z.of_nat (length s) -> f j = nth (Z.to_nat j) (s ++ [0]) 0.

(** The bytes before c agree and are not 0: what strcmp has seen. *)
Definition same_upto (f1 f2 : Z -> Z) (c : Z) : Prop :=
  forall j, 0 <= j < c -> f1 j = f2 j /\ f1 j <> 0.

(** Where f1 is 0 or f1 and f2 differ: strcmp stops there. *)
Definition stop_at (f1 f2 : Z -> Z) (i : Z) : Prop := f1 i = 0 \/ f1 i <> f2 i.

(** At the first stop i of byte functions that agree with the strings,
    strings of nonzero bytes, the answer is the difference of their bytes
    at i. *)
Lemma strcmp_res_stop s1 s2 f1 f2 i :
  Forall (fun c => c <> 0) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> 0 <= i -> same_upto f1 f2 i ->
  stop_at f1 f2 i -> strcmp_res s1 s2 = (f1 i - f2 i) mod 2 ^ 32.
Proof.
  revert s2 f1 f2 i. induction s1 as [|c1 s1 IH]; intros s2 f1 f2 i Hn A1 A2 Hi Hs Hst.
  - assert (E1 : f1 0 = 0) by (rewrite A1; cbn; [reflexivity | lia]).
    destruct (Z.eq_dec i 0) as [->|Hne]; [|destruct (Hs 0 ltac:(lia)); contradiction].
    rewrite E1. destruct s2 as [|c2 s2]; cbn [strcmp_res]; rewrite (A2 0); cbn [length]; try lia; reflexivity.
  - apply Forall_cons_1 in Hn as [Hc1 Hn].
    assert (E1 : f1 0 = c1) by (rewrite A1; cbn [length]; [reflexivity | lia]).
    destruct s2 as [|c2 s2].
    + assert (E2 : f2 0 = 0) by (rewrite A2; cbn; [reflexivity | lia]).
      destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite E1 E2; reflexivity|].
      destruct (Hs 0 ltac:(lia)) as [Ha Hb]. congruence.
    + assert (E2 : f2 0 = c2) by (rewrite A2; cbn [length]; [reflexivity | lia]).
      cbn [strcmp_res]. destruct (Z.eq_dec i 0) as [->|Hne].
      * rewrite E1 E2. destruct Hst as [Hz|Hd]; [congruence|].
        replace (c1 =? c2) with false by (symmetry; apply Z.eqb_neq; congruence). reflexivity.
      * destruct (Hs 0 ltac:(lia)) as [Ha _]. replace (c1 =? c2) with true by (symmetry; apply Z.eqb_eq; congruence).
        replace (f1 i - f2 i) with (f1 (i - 1 + 1) - f2 (i - 1 + 1)) by (f_equal; f_equal; lia).
        apply (IH s2 (fun j => f1 (j + 1)) (fun j => f2 (j + 1)) (i - 1) Hn).
        { intros j Hj. rewrite A1; [|cbn [length]; lia]. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
          reflexivity. }
        { intros j Hj. rewrite A2; [|cbn [length]; lia]. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
          reflexivity. }
        { lia. }
        { intros j Hj. apply Hs. lia. }
        { unfold stop_at in *. replace (i - 1 + 1) with i by lia. exact Hst. }
Qed.

(** A byte function that agrees with the string s and is not 0 below c
    reaches no further than s's NUL: c is at most s's length. *)
Lemma nonzero_len f s c : agree_str f s -> (forall j, 0 <= j < c -> f j <> 0) -> c <= Z.of_nat (length s).
Proof.
  intros A H. destruct (Z.le_gt_cases c (Z.of_nat (length s))) as [Hc|Hc]; [exact Hc|].
  exfalso. apply (H (Z.of_nat (length s))); [lia|]. rewrite A; [|lia].
  rewrite Nat2Z.id app_nth2; [|lia]. rewrite Nat.sub_diag. reflexivity.
Qed.

(** What strcmp has seen lies inside both strings. *)
Lemma same_upto_len f1 f2 s1 s2 c : agree_str f1 s1 -> agree_str f2 s2 -> same_upto f1 f2 c ->
  c <= Z.of_nat (length s1) /\ c <= Z.of_nat (length s2).
Proof.
  intros A1 A2 H. split.
  - apply (nonzero_len f1 s1 c A1). intros j Hj. apply H, Hj.
  - apply (nonzero_len f2 s2 c A2). intros j Hj. destruct (H j Hj). congruence.
Qed.

(** A stop exists at or before any index where f1 is 0 or the two differ,
    among indices from c: the first one. *)
Lemma first_stop f1 f2 c z : 0 <= c <= z -> stop_at f1 f2 z -> same_upto f1 f2 c ->
  exists i, c <= i <= z /\ stop_at f1 f2 i /\ same_upto f1 f2 i.
Proof.
  intros Hz Hst Hs.
  assert (H : forall n : nat, same_upto f1 f2 (c + Z.of_nat n) \/
                exists i, c <= i < c + Z.of_nat n /\ stop_at f1 f2 i /\ same_upto f1 f2 i).
  { induction n as [|n [IH|IH]]; [left; rewrite Z.add_0_r; exact Hs| |right].
    - destruct (Z.eq_dec (f1 (c + Z.of_nat n)) 0) as [E|Ne];
        [|destruct (Z.eq_dec (f1 (c + Z.of_nat n)) (f2 (c + Z.of_nat n))) as [E'|Ne']].
      + right. exists (c + Z.of_nat n). split; [lia|]. split; [left; exact E | exact IH].
      + left. intros j Hj. destruct (Z.eq_dec j (c + Z.of_nat n)) as [->|Hne]; [split; assumption|].
        apply IH. lia.
      + right. exists (c + Z.of_nat n). split; [lia|]. split; [right; exact Ne' | exact IH].
    - destruct IH as (i & Hi & H1 & H2). exists i. split; [lia|]. auto. }
  destruct (H (Z.to_nat (z - c) + 1)%nat) as [Hall|(i & Hi & H1 & H2)].
  - exfalso. destruct (Hall z ltac:(lia)) as [E Hn]. destruct Hst; contradiction.
  - exists i. split; [lia|]. auto.
Qed.

(** ## Bytes of a window *)

(** Word q of the words ws, or 0 past them. *)
Definition wrd (ws : list Z) (q : Z) : Z := nth (Z.to_nat q) ws 0.

(** Byte i of the words ws, little-endian, in order. *)
Definition bt (ws : list Z) (i : Z) : Z := byte_of (wrd ws (i / 8)) (i mod 8).

(** Byte j of the word q of ws is [bt] ws (8q + j). *)
Lemma bt_word ws q j : 0 <= q -> 0 <= j < 8 -> byte_of (wrd ws q) j = bt ws (8 * q + j).
Proof.
  intros Hq Hj. unfold bt. replace ((8 * q + j) / 8) with q by (Z.div_mod_to_equations; lia).
  replace ((8 * q + j) mod 8) with j by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

(** [bt] is the window's byte list [wbytes] read at i. *)
Lemma wbytes_bt ws i : 0 <= i < 8 * Z.of_nat (length ws) -> wbytes ws !! Z.to_nat i = Some (bt ws i).
Proof.
  revert i. induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct (Z.lt_ge_cases i 8) as [H8|H8].
  - rewrite wbytes_head; [|lia]. unfold bt, wrd. rewrite Z.div_small; [|lia]. rewrite Z.mod_small; [|lia].
    rewrite Z2Nat.id; [reflexivity | lia].
  - replace (Z.to_nat i) with (8 + Z.to_nat (i - 8))%nat by lia. rewrite wbytes_tail IH; [|lia].
    unfold bt, wrd. replace (i / 8) with ((i - 8) / 8 + 1) by (Z.div_mod_to_equations; lia).
    replace (i mod 8) with ((i - 8) mod 8) by (Z.div_mod_to_equations; lia).
    replace (Z.to_nat ((i - 8) / 8 + 1)) with (S (Z.to_nat ((i - 8) / 8)))
      by (pose proof (Z.div_pos (i - 8) 8); lia). reflexivity.
Qed.

(** A string's bytes from p, through its NUL, are its window's bytes
    from p's offset in its word. *)
Lemma str_bt p b reg ws s : str_shape p b reg ws s -> agree_str (fun j => bt ws (ptr_addr p mod 8 + j)) s.
Proof.
  intros Hs j Hj. pose proof (str_shape_byte p b reg ws s (Z.to_nat j) Hs ltac:(lia)) as E.
  pose proof (ss_len _ _ _ _ _ Hs) as Hl. pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  replace (Z.to_nat (ptr_addr p mod 8) + Z.to_nat j)%nat with (Z.to_nat (ptr_addr p mod 8 + j)) in E by lia.
  rewrite wbytes_bt in E; [|Z.div_mod_to_equations; lia].
  rewrite (nth_lookup_Some (s ++ [0]) (Z.to_nat j) 0 (bt ws (ptr_addr p mod 8 + j))); [reflexivity|].
  rewrite <- E. reflexivity.
Qed.

(** ## The words' masks *)

(** A word's bytes are all nonzero exactly when its [loop_mask], glibc's
    `has_zero`, is 0. *)
Lemma loop_mask_zero w : 0 <= w < 2 ^ 64 -> (loop_mask w = 0 <-> forall j, 0 <= j < 8 -> byte_of w j <> 0).
Proof.
  intros Hw. split.
  - intros E j Hj Hz.
    destruct (first_stop (byte_of w) (byte_of w) 0 j ltac:(lia) (or_introl Hz) ltac:(intros i Hi; lia))
      as (i & Hi & [Hz'|Hd] & Hs); [|contradiction].
    pose proof (loop_mask_at w i ltac:(lia) ltac:(intros k Hk; apply Hs; exact Hk) Hz') as H.
    rewrite E in H. unfold byte_of in H. rewrite Z.div_0_l in H; [discriminate | apply Z.pow_nonzero; lia].
  - intros H. apply zero_word; [apply loop_mask_range|]. intros j Hj. apply (loop_mask_below w 8 j); [lia | | exact Hj].
    intros k Hk. apply H, Hk.
Qed.

(** Word q of the 64-bit words ws is in range. *)
Lemma wrd_range ws q : Forall (fun w => 0 <= w < 2 ^ 64) ws -> 0 <= wrd ws q < 2 ^ 64.
Proof.
  intros H. unfold wrd. destruct (Nat.lt_ge_cases (Z.to_nat q) (length ws)) as [Hq|Hq].
  - rewrite Forall_forall in H. apply H, nth_In, Hq.
  - rewrite nth_overflow; [lia | exact Hq].
Qed.

(** For a decidable P, every index below n has P or one lacks it. *)
Lemma idx_dec (P : Z -> Prop) (dec : forall j, {P j} + {~ P j}) (n : nat) :
  (forall j, 0 <= j < Z.of_nat n -> P j) \/ exists j, 0 <= j < Z.of_nat n /\ ~ P j.
Proof.
  induction n as [|n [IH|IH]].
  - left. intros j Hj. lia.
  - destruct (dec (Z.of_nat n)) as [H|H].
    + left. intros j Hj. destruct (Z.eq_dec j (Z.of_nat n)) as [->|Hne]; [exact H | apply IH; lia].
    + right. exists (Z.of_nat n). split; [lia | exact H].
  - right. destruct IH as (j & Hj & H). exists j. split; [lia | exact H].
Qed.

(** Two different 64-bit words differ in a byte. *)
Lemma words_differ x y : 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y ->
  exists t, 0 <= t < 8 /\ byte_of x t <> byte_of y t.
Proof.
  intros Hx Hy Hne. destruct (idx_dec (fun t => byte_of x t = byte_of y t) (fun t => Z.eq_dec _ _) 8) as [H|H].
  - exfalso. apply Hne. rewrite -(of_bytes_byte_of x Hx) -(of_bytes_byte_of y Hy). cbn [map idx8].
    rewrite (H 0) ?(H 1) ?(H 2) ?(H 3) ?(H 4) ?(H 5) ?(H 6) ?(H 7); cbn; lia.
  - destruct H as (t & Ht & H). exists t. split; [cbn in Ht; lia | exact H].
Qed.

(** A 64-bit word whose [loop_mask] is not 0 has a zero byte. *)
Lemma loop_mask_has_zero w : 0 <= w < 2 ^ 64 -> loop_mask w <> 0 -> exists j, 0 <= j < 8 /\ byte_of w j = 0.
Proof.
  intros Hw Hm. destruct (idx_dec (fun j => byte_of w j <> 0) (fun j => match Z.eq_dec (byte_of w j) 0 with left e => right (fun h => h e) | right n => left n end) 8) as [H|H].
  - exfalso. apply Hm, (loop_mask_zero w Hw). intros j Hj. apply H. cbn. lia.
  - destruct H as (j & Hj & H). exists j. split; [cbn in Hj; lia | lia].
Qed.

(** An or of 64-bit words is a 64-bit word. *)
Lemma lor_range a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
  intros Ha Hb. assert (E : Z.lor a b mod 2 ^ 64 = Z.lor a b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_mod_pow2; [|lia]. rewrite Z.lor_spec.
    destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E.
    rewrite (bits64 a n Ha E) (bits64 b n Hb E). reflexivity. }
  rewrite -E. apply Z.mod_pos_bound. lia.
Qed.

(** ## The comparison mask *)

(** glibc's `find_zero_ne_all` (string-fzc.h) on the words x and y, as
    nanofil's IR computes it, every read wrapped: 128 in each byte where
    x's is 0 or x's and y's differ, else 0 ([cmp_mask_byte]). *)
Definition cmp_mask (x y : Z) : Z :=
  Z.land
    (Z.lor
       (Z.lor
          (((Z.land (Z.lxor (x mod 2 ^ 64) (y mod 2 ^ 64) mod 2 ^ 64) (9187201950435737471 mod 2 ^ 64)
               mod 2 ^ 64 + 9187201950435737471 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64)
          (Z.lxor (x mod 2 ^ 64) (y mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64)
       (Z.lxor
          (Z.lor
             (((Z.land (x mod 2 ^ 64) (9187201950435737471 mod 2 ^ 64) mod 2 ^ 64
                + 9187201950435737471 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64)
             (x mod 2 ^ 64) mod 2 ^ 64)
          (-1 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64)
    (9259542123273814144 mod 2 ^ 64).

(** A byte of a word's low seven bits plus 127 does not carry. *)
Lemma add_ones7 z i : 0 <= i < 8 -> byte_of (Z.land z ones7 mod 2 ^ 64 + ones7) i = Z.land (byte_of z i) 127 + 127.
Proof.
  intros Hi. rewrite byte_of_add; [| |lia].
  - rewrite byte_of_mod64; [|lia]. rewrite byte_of_land; [|lia]. rewrite byte_ones7; [reflexivity|lia].
  - intros j Hj. rewrite byte_of_mod64; [|lia]. rewrite byte_of_land; [|lia]. rewrite byte_ones7; [|lia].
    pose proof (land127 (byte_of z j) (byte_of_range z j)). lia.
Qed.

(** The comparison mask's byte, on two bytes, checked on all 65536
    pairs. *)
Lemma cmp_on_bytes b1 b2 : 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  Z.land (Z.lor (Z.lor (Z.land (Z.lxor b1 b2) 127 + 127) (Z.lxor b1 b2))
            (Z.lxor (Z.lor (Z.land b1 127 + 127) b1) 255)) 128 =
  if (b1 =? 0) || negb (b1 =? b2) then 128 else 0.
Proof.
  intros H1 H2. apply Z.eqb_eq.
  set (P := fun b1 b2 => Z.land (Z.lor (Z.lor (Z.land (Z.lxor b1 b2) 127 + 127) (Z.lxor b1 b2))
            (Z.lxor (Z.lor (Z.land b1 127 + 127) b1) 255)) 128 =? if (b1 =? 0) || negb (b1 =? b2) then 128 else 0).
  assert (H : forallb (fun b1 => forallb (P b1) (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  exact (all_bytes (P b1) (all_bytes _ H b1 H1) b2 H2).
Qed.

(** Byte i of the comparison mask: 128 where x's byte is 0 or differs
    from y's, else 0. *)
Lemma cmp_mask_byte x y i : 0 <= i < 8 ->
  byte_of (cmp_mask x y) i = if (byte_of x i =? 0) || negb (byte_of x i =? byte_of y i) then 128 else 0.
Proof.
  intros Hi. assert (Hi0 : 0 <= i) by lia. unfold cmp_mask.
  change (9187201950435737471 mod 2 ^ 64) with ones7. change (9259542123273814144 mod 2 ^ 64) with highs.
  change (-1 mod 2 ^ 64) with all64.
  pose proof (fun z => byte_of_mod64 z i Hi) as M. pose proof (fun a b => byte_of_land a b i Hi0) as La.
  pose proof (fun a b => byte_of_lor a b i Hi0) as Lo. pose proof (fun a b => byte_of_lxor a b i Hi0) as Lx.
  pose proof (fun z => add_ones7 z i Hi) as Ad.
  do 6 rewrite ?M ?La ?Lo ?Lx ?Ad ?(byte_ones7 i Hi) ?(byte_highs i Hi) ?(byte_all64 i Hi).
  apply cmp_on_bytes; apply byte_of_range.
Qed.

(** The comparison mask is a 64-bit word. *)
Lemma cmp_mask_range x y : 0 <= cmp_mask x y < 2 ^ 64.
Proof. unfold cmp_mask. apply land_range; [apply Z.mod_pos_bound; lia | vm_compute; split; congruence]. Qed.

(** ## Words of an unaligned string *)

(** The word lo shifted down o bytes, as nanofil's IR computes it: its
    bytes from o, then zeros. *)
Definition shd (lo o : Z) : Z := (lo mod 2 ^ 64 / 2 ^ (((8 * o) mod 2 ^ 32) mod 64)) mod 2 ^ 64.

(** The word hi shifted up 8 - o bytes, as nanofil's IR computes it:
    zeros, then its first o bytes. *)
Definition shu (hi o : Z) : Z := ((hi mod 2 ^ 64 * 2 ^ (((64 - 8 * o) mod 2 ^ 32) mod 64)) mod 2 ^ 64) mod 2 ^ 64.

(** glibc's `MERGE` (strcmp.c) of the words lo and hi for a string at
    offset o of its word: the eight bytes from byte o of lo on. *)
Definition merge (lo hi o : Z) : Z := Z.lor (shd lo o) (shu hi o).

(** A shift up by k whole bytes moves byte i - k to byte i. *)
Lemma byte_of_mul_pow z k i : 0 <= k -> 0 <= i ->
  byte_of (z * 2 ^ (8 * k)) i = if i <? k then 0 else byte_of z (i - k).
Proof.
  intros Hk Hi. unfold byte_of. destruct (Z.ltb_spec i k) as [Hlt|Hge].
  - replace (z * 2 ^ (8 * k)) with (z * 2 ^ (8 * (k - i - 1)) * 256 * 2 ^ (8 * i)).
    + rewrite Z.div_mul; [|apply Z.pow_nonzero; lia]. apply Z.mod_mul. lia.
    + replace (8 * k) with (8 * (k - i - 1) + 8 + 8 * i) by lia.
      rewrite Z.pow_add_r; [|lia|lia]. rewrite Z.pow_add_r; [|lia|lia]. change (2 ^ 8) with 256. ring.
  - replace (2 ^ (8 * i)) with (2 ^ (8 * k) * 2 ^ (8 * (i - k))).
    + assert (P1 : 0 < 2 ^ (8 * k)) by (apply Z.pow_pos_nonneg; lia).
      assert (P2 : 0 < 2 ^ (8 * (i - k))) by (apply Z.pow_pos_nonneg; lia).
      rewrite -(Z.div_div (z * 2 ^ (8 * k)) (2 ^ (8 * k)) (2 ^ (8 * (i - k))) ltac:(lia) ltac:(lia)). rewrite (Z.div_mul z (2 ^ (8 * k))); [reflexivity | lia].
    + rewrite -Z.pow_add_r; [f_equal; lia | lia | lia].
Qed.

(** Byte u of lo shifted down o bytes. *)
Lemma shd_byte lo o u : 0 <= o < 8 -> 0 <= u < 8 ->
  byte_of (shd lo o) u = if u + o <? 8 then byte_of lo (u + o) else 0.
Proof.
  intros Ho Hu. unfold shd. rewrite (Z.mod_small (8 * o) (2 ^ 32)); [|lia]. rewrite (Z.mod_small (8 * o) 64); [|lia].
  rewrite byte_of_mod64; [|lia]. rewrite byte_of_div; [|lia|lia]. destruct (Z.ltb_spec (u + o) 8).
  - apply byte_of_mod64. lia.
  - apply byte_of_high; [apply Z.mod_pos_bound; lia | lia].
Qed.

(** Byte u of hi shifted up 8 - o bytes. *)
Lemma shu_byte hi o u : 0 < o < 8 -> 0 <= u < 8 ->
  byte_of (shu hi o) u = if u + o <? 8 then 0 else byte_of hi (u + o - 8).
Proof.
  intros Ho Hu. unfold shu. rewrite (Z.mod_small (64 - 8 * o) (2 ^ 32)); [|lia].
  rewrite (Z.mod_small (64 - 8 * o) 64); [|lia]. replace (64 - 8 * o) with (8 * (8 - o)) by lia.
  rewrite byte_of_mod64; [|lia]. rewrite byte_of_mod64; [|lia]. rewrite byte_of_mul_pow; [|lia|lia].
  destruct (Z.ltb_spec u (8 - o)), (Z.ltb_spec (u + o) 8); try lia.
  rewrite byte_of_mod64; [|lia]. f_equal. lia.
Qed.

(** Byte u of [merge] lo hi o: byte u + o of the bytes of lo then hi. *)
Lemma merge_byte lo hi o u : 0 < o < 8 -> 0 <= u < 8 ->
  byte_of (merge lo hi o) u = if u + o <? 8 then byte_of lo (u + o) else byte_of hi (u + o - 8).
Proof.
  intros Ho Hu. unfold merge. rewrite byte_of_lor; [|lia]. rewrite shd_byte; [|lia|lia]. rewrite shu_byte; [|lia|lia].
  destruct (u + o <? 8); [apply Z.lor_0_r | apply Z.lor_0_l].
Qed.

(** [merge] is a 64-bit word. *)
Lemma merge_range lo hi o : 0 <= merge lo hi o < 2 ^ 64.
Proof. apply lor_range; apply Z.mod_pos_bound; lia. Qed.

(** ## Arithmetic of the IR *)

(** The low three bits of an address: an and with 7. *)
Lemma land7 x : 0 <= x < 2 ^ 64 -> Z.land (x mod 2 ^ 64) (7 mod 2 ^ 64) = x mod 8.
Proof.
  intros H. rewrite (Z.mod_small x); [|lia]. change (7 mod 2 ^ 64) with (Z.ones 3).
  rewrite Z.land_ones; [reflexivity|lia].
Qed.

(** The bytes from a to its next 8-aligned address: -a and 7. *)
Lemma neg_land7 a : 0 <= a < 2 ^ 64 -> Z.land ((- (a mod 2 ^ 64)) mod 2 ^ 64 mod 2 ^ 64) (7 mod 2 ^ 64) = (- a) mod 8.
Proof.
  intros H. rewrite (Z.mod_small a); [|lia]. rewrite Zmod_mod. change (7 mod 2 ^ 64) with (Z.ones 3).
  rewrite Z.land_ones; [|lia]. change (2 ^ 3) with 8. symmetry.
  apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 61); reflexivity].
Qed.

(** A byte loaded signed into a `w` and extended unsigned is the byte. *)
Lemma sb_ub c : 0 <= c < 256 -> extension Ub ((extension Sb c mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32 = c.
Proof.
  intros H. apply Z.eqb_eq.
  exact (all_bytes (fun c => extension Ub ((extension Sb c mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32 =? c)
           ltac:(vm_compute; reflexivity) c H).
Qed.

(** A small `w` counter, extended signed to an `l`, is itself. *)
Lemma sext_small c : 0 <= c < 2 ^ 31 -> extension Sw (c mod 2 ^ 32) mod 2 ^ 64 = c.
Proof.
  intros H. rewrite (Z.mod_small c); [|lia]. cbn [extension]. unfold sign_extension.
  rewrite (Z.mod_small c); [|lia]. replace (2 ^ 31 <=? c) with false; [apply Z.mod_small; lia|].
  symmetry. apply Z.leb_gt. lia.
Qed.

(** Byte j of x, as the IR takes it: x shifted down 8j bits, extended
    unsigned from its low byte. *)
Lemma ub_shift x j : 0 <= j < 8 ->
  extension Ub ((x mod 2 ^ 64 / 2 ^ (((8 * j) mod 2 ^ 32) mod 64)) mod 2 ^ 32) mod 2 ^ 32 = byte_of x j.
Proof.
  intros Hj. rewrite (Z.mod_small (8 * j) (2 ^ 32)); [|lia]. rewrite (Z.mod_small (8 * j) 64); [|lia].
  cbn [extension]. rewrite -(byte_of_mod64 x j Hj). unfold byte_of.
  rewrite -(Znumtheory.Zmod_div_mod 256 (2 ^ 32)); [| lia | lia | exists (2 ^ 24); reflexivity].
  apply Z.mod_small. pose proof (Z.mod_pos_bound (x mod 2 ^ 64 / 2 ^ (8 * j)) 256). lia.
Qed.

(** ## A string's window *)

(** The arithmetic of a string's shape: its object, its window's start
    and end, and its length inside the window. *)
Lemma shape_facts p b reg ws s : str_shape p b reg ws s ->
  0 < b /\ b <= wstart p /\ wstart p mod 8 = 0 /\ ptr_addr p = wstart p + ptr_addr p mod 8 /\
  0 <= ptr_addr p mod 8 < 8 /\ wstart p + 8 * Z.of_nat (length ws) <= r_end reg /\ r_end reg <= 2 ^ 48 /\
  ptr_addr p mod 8 + Z.of_nat (length s) < 8 * Z.of_nat (length ws) /\ (ptr_cap p = Obj b \/ ptr_cap p = Ro b).
Proof.
  intros [Hc Hb0 Hb8 Hst Hf Hsp Hl Hw Hby Hch]. unfold wstart in *.
  pose proof (Z.div_mod (ptr_addr p) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  pose proof (Z.div_mod b 8 ltac:(lia)).
  pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  split; [lia|]. split; [nia|]. split.
  { replace (ptr_addr p - ptr_addr p mod 8) with (8 * (ptr_addr p / 8)) by lia. rewrite Z.mul_comm. apply Z_mod_mult. }
  repeat split; try lia. exact Hc.
Qed.

(** Bytes c to c + 7 of a string at offset k of its window, where k + c
    = 8q, are word q's. *)
Lemma bt_at ws k c q u : k + c = 8 * q -> 0 <= q -> 0 <= u < 8 -> bt ws (k + (c + u)) = byte_of (wrd ws q) u.
Proof. intros E Hq Hu. rewrite (bt_word ws q u Hq Hu). f_equal. lia. Qed.

(** Bytes c to c + 7 of a string at offset k of its window, where
    k + c = 8q + o: [merge] of words q and q + 1. *)
Lemma bt_merge ws k c q o u : k + c = 8 * q + o -> 0 <= q -> 0 < o < 8 -> 0 <= u < 8 ->
  bt ws (k + (c + u)) = byte_of (merge (wrd ws q) (wrd ws (q + 1)) o) u.
Proof.
  intros E Hq Ho Hu. rewrite merge_byte; [|lia|lia]. destruct (Z.ltb_spec (u + o) 8).
  - rewrite (bt_word ws q (u + o)); [|lia|lia]. f_equal. lia.
  - rewrite (bt_word ws (q + 1) (u + o - 8)); [|lia|lia]. f_equal. lia.
Qed.

(** ## Returns *)

(** Where the bytes of x and y are a string's from c, a first stop below
    n of them is the first stop of the strings: strcmp's answer is the
    difference of their bytes there. *)
Lemma word_stop s1 s2 f1 f2 c x y n :
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> 0 <= c -> same_upto f1 f2 c ->
  n <= 8 -> (forall u, 0 <= u < n -> f1 (c + u) = byte_of x u /\ f2 (c + u) = byte_of y u) ->
  (exists u, 0 <= u < n /\ stop_at (byte_of x) (byte_of y) u) ->
  exists j, 0 <= j < n /\ stop_at (byte_of x) (byte_of y) j /\ same_upto (byte_of x) (byte_of y) j /\
    strcmp_res s1 s2 = (byte_of x j - byte_of y j) mod 2 ^ 32.
Proof.
  intros Hc A1 A2 H0 Hs Hn Hb (u & Hu & Hst).
  destruct (first_stop (byte_of x) (byte_of y) 0 u ltac:(lia) Hst ltac:(intros j Hj; exfalso; lia))
    as (j & Hj & Hstj & Hsj).
  exists j. split; [lia|]. split; [exact Hstj|]. split; [exact Hsj|].
  destruct (Hb j ltac:(lia)) as [E1 E2]. rewrite -E1 -E2.
  apply strcmp_res_stop; [ | exact A1 | exact A2 | lia | | ].
  - eapply Forall_impl; [| exact Hc]. cbn. intros; lia.
  - intros i Hi. destruct (Z.lt_ge_cases i c); [apply Hs; lia|].
    destruct (Hb (i - c) ltac:(lia)) as [F1 F2]. replace (c + (i - c)) with i in F1, F2 by lia.
    rewrite F1 F2. apply Hsj. lia.
  - unfold stop_at in *. rewrite E1 E2. exact Hstj.
Qed.

(** Where both strings' bytes from c are those of one word with a zero
    byte, the strings are equal: strcmp's answer is 0. *)
Lemma word_zero s1 s2 f1 f2 c x :
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> 0 <= c -> same_upto f1 f2 c ->
  0 <= x < 2 ^ 64 -> (forall u, 0 <= u < 8 -> f1 (c + u) = byte_of x u /\ f2 (c + u) = byte_of x u) ->
  loop_mask x <> 0 -> strcmp_res s1 s2 = 0.
Proof.
  intros Hc A1 A2 H0 Hs Hx Hb Hm. destruct (loop_mask_has_zero x Hx Hm) as (u & Hu & Hz).
  destruct (word_stop s1 s2 f1 f2 c x x 8 Hc A1 A2 H0 Hs ltac:(lia) Hb) as (j & _ & _ & _ & ->).
  - exists u. split; [exact Hu | left; exact Hz].
  - rewrite Z.sub_diag. reflexivity.
Qed.

(** Where the strings' bytes from c are those of x and y, equal and not
    0, strcmp has seen 8 more bytes. *)
Lemma word_same f1 f2 c x y : 0 <= c -> same_upto f1 f2 c ->
  (forall u, 0 <= u < 8 -> f1 (c + u) = byte_of x u /\ f2 (c + u) = byte_of y u) ->
  (forall u, 0 <= u < 8 -> byte_of x u = byte_of y u /\ byte_of x u <> 0) -> same_upto f1 f2 (c + 8).
Proof.
  intros H0 Hs Hb Hxy i Hi. destruct (Z.lt_ge_cases i c); [apply Hs; lia|].
  destruct (Hb (i - c) ltac:(lia)) as [F1 F2]. replace (c + (i - c)) with i in F1, F2 by lia.
  rewrite F1 F2. apply Hxy. lia.
Qed.

(** At the first stop j of the bytes of x and y, the comparison mask's
    population count ([tail]) is 8j + 7, and the mask is not 0. *)
Lemma cmp_mask_first x y j : 0 <= j < 8 -> stop_at (byte_of x) (byte_of y) j -> same_upto (byte_of x) (byte_of y) j ->
  tail (cmp_mask x y) = 8 * j + 7 /\ cmp_mask x y <> 0.
Proof.
  intros Hj Hst Hs.
  assert (Hat : byte_of (cmp_mask x y) j = 128).
  { rewrite cmp_mask_byte; [|lia]. destruct Hst as [E|E].
    - rewrite E. reflexivity.
    - replace (byte_of x j =? byte_of y j) with false; [rewrite orb_true_r; reflexivity|].
      symmetry. apply Z.eqb_neq. exact E. }
  split.
  - apply tail_first; [apply cmp_mask_range | | exact Hj | exact Hat |].
    + intros i Hi. rewrite cmp_mask_byte; [|lia]. destruct (_ || _); auto.
    + intros i Hi. rewrite cmp_mask_byte; [|lia]. destruct (Hs i Hi) as [E1 E2].
      replace (byte_of x i =? 0) with false; [|symmetry; apply Z.eqb_neq; exact E2].
      replace (byte_of x i =? byte_of y i) with true; [reflexivity|symmetry; apply Z.eqb_eq; exact E1].
  - intros E. rewrite E in Hat. unfold byte_of in Hat. rewrite Z.div_0_l in Hat; [discriminate | apply Z.pow_nonzero; lia].
Qed.

(** Byte j of the string at p whose window is ws. *)
Definition sbyte (p : ptr) (ws : list Z) (j : Z) : Z := bt ws (ptr_addr p mod 8 + j).

(** A string's bytes through its NUL are [sbyte]'s. *)
Lemma sbyte_agree p b reg ws s : str_shape p b reg ws s -> agree_str (sbyte p ws) s.
Proof. exact (str_bt p b reg ws s). Qed.

(** The word lo shifted down o bytes is a 64-bit word. *)
Lemma shd_mod lo o : shd lo o mod 2 ^ 64 = shd lo o.
Proof. apply Zmod_mod. Qed.
