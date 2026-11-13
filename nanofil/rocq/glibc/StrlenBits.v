(** Glibc's `c: strlen` scans eight bytes at a time instead of reading
    one byte per iteration. It loads an aligned 64-bit [[word]], applies
    a bitmask that turns every zero byte into `0x80` and every nonzero
    byte into `0x00`, and then locates the lowest set bit with a
    population count.

    Verifying glibc's IR in [StrlenLogic](StrlenLogic.v) requires
    connecting 64-bit arithmetic and bitwise operations back to
    individual bytes. Here we reduce every word-level operation in the
    first word and the loop to byte-level statements over [byte_of],
    then discharge each single-byte identity by computing over all 256
    byte values. *)

From Stdlib Require Import ZArith Lia List Bool.
From Nanofil Require Import Memory.
Import ListNotations.
Open Scope Z_scope.

(** ## Bytes of a word

    Bitwise operations and whole-byte shifts in C operate independently
    on each byte of a 64-bit [[word]], while arithmetic wraps modulo
    2^64. The lemmas in this section lift [byte_of] over those
    operations so later proofs can reason one byte at a time. *)

(** Bit n of byte i in x equals bit 8 * i + n of x whenever n is below
    8, as [byte_of_bits] proves. *)
Lemma byte_of_bits x i n : 0 <= i -> 0 <= n ->
  Z.testbit (byte_of x i) n = (n <? 8) && Z.testbit x (n + 8 * i).
Proof.
  intros Hi Hn. unfold byte_of. change 256 with (2 ^ 8).
  rewrite Z.testbit_mod_pow2 by lia. rewrite <- Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftr_spec by lia. reflexivity.
Qed.

(** [byte_of_land] shows that byte i of a bitwise conjunction equals the
    conjunction of the two input bytes. *)
Lemma byte_of_land x y i : 0 <= i -> byte_of (Z.land x y) i = Z.land (byte_of x i) (byte_of y i).
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, !byte_of_bits, Z.land_spec by lia. destruct (n <? 8); reflexivity.
Qed.

(** [byte_of_lor] shows that byte i of a bitwise disjunction equals the
    disjunction of the two input bytes. *)
Lemma byte_of_lor x y i : 0 <= i -> byte_of (Z.lor x y) i = Z.lor (byte_of x i) (byte_of y i).
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lor_spec, !byte_of_bits, Z.lor_spec by lia. destruct (n <? 8); reflexivity.
Qed.

(** [byte_of_lxor] shows that byte i of a bitwise exclusive-or equals
    the exclusive-or of the two input bytes. *)
Lemma byte_of_lxor x y i : 0 <= i -> byte_of (Z.lxor x y) i = Z.lxor (byte_of x i) (byte_of y i).
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, !byte_of_bits, Z.lxor_spec by lia. destruct (n <? 8); reflexivity.
Qed.

(** Wrapping an integer modulo 2^64 preserves its low eight bytes, as
    [byte_of_mod64] verifies. *)
Lemma byte_of_mod64 z i : 0 <= i < 8 -> byte_of (z mod 2 ^ 64) i = byte_of z i.
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite !byte_of_bits, Z.testbit_mod_pow2 by lia.
  destruct (n <? 8) eqn:E; [|reflexivity]. apply Z.ltb_lt in E.
  replace (n + 8 * i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(** Shifting an integer right by k whole bytes moves byte i + k down to
    position i, as [byte_of_div] proves. *)
Lemma byte_of_div z k i : 0 <= k -> 0 <= i -> byte_of (z / 2 ^ (8 * k)) i = byte_of z (i + k).
Proof.
  intros Hk Hi. unfold byte_of. rewrite Z.div_div by (apply Z.pow_nonzero || apply Z.pow_pos_nonneg; lia).
  rewrite <- Z.pow_add_r by lia. do 3 f_equal. lia.
Qed.

(** A 64-bit unsigned integer has zero in every byte from index 8
    onward, as [byte_of_high] states. *)
Lemma byte_of_high z i : 0 <= z < 2 ^ 64 -> 8 <= i -> byte_of z i = 0.
Proof.
  intros Hz Hi. unfold byte_of. rewrite Z.div_small; [reflexivity|].
  split; [lia|]. apply (Z.lt_le_trans _ (2 ^ 64)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(** Every byte returned by [byte_of] lies between 0 and 255 inclusive,
    as [byte_of_range] records. *)
Lemma byte_of_range z i : 0 <= byte_of z i < 256.
Proof. unfold byte_of. apply Z.mod_pos_bound. lia. Qed.

(** [low_step] splits the low n + 1 bytes of z into its low n bytes plus
    byte n shifted into place. *)
Lemma low_step z n : 0 <= n ->
  z mod 2 ^ (8 * (n + 1)) = z mod 2 ^ (8 * n) + 2 ^ (8 * n) * byte_of z n.
Proof.
  intros Hn. replace (2 ^ (8 * (n + 1))) with (2 ^ (8 * n) * 256)
    by (rewrite Z.mul_add_distr_l, Z.pow_add_r by lia; reflexivity).
  rewrite Z.rem_mul_r by (lia || (pose proof (Z.pow_pos_nonneg 2 (8 * n)); lia)). reflexivity.
Qed.

(** ## Sums and differences byte by byte

    Both of glibc's zero-byte masks combine addition or subtraction with
    bitwise masks. When no carry crosses a byte boundary in an addition,
    or no borrow crosses below the first zero byte in a subtraction, the
    word-level sum or difference acts independently on each byte. *)

(** When every byte pair of u and v sums to less than 256, [add_low]
    proves by induction that no prefix carries into the next byte. *)
Lemma add_low u v n : 0 <= n <= 8 ->
  (forall i, 0 <= i < 8 -> byte_of u i + byte_of v i < 256) ->
  u mod 2 ^ (8 * n) + v mod 2 ^ (8 * n) < 2 ^ (8 * n).
Proof.
  intros [H0 H8] Hb. revert H8. pattern n. apply natlike_ind; [| |exact H0].
  - intros _. rewrite Z.mul_0_r, Z.pow_0_r, !Z.mod_1_r. lia.
  - intros k Hk IH H8. unfold Z.succ in *. rewrite !low_step by lia.
    assert (Hp : 0 < 2 ^ (8 * k)) by (apply Z.pow_pos_nonneg; lia).
    replace (2 ^ (8 * (k + 1))) with (2 ^ (8 * k) * 256)
      by (rewrite Z.mul_add_distr_l, Z.pow_add_r by lia; reflexivity).
    specialize (IH ltac:(lia)). specialize (Hb k ltac:(lia)). nia.
Qed.

(** When no byte pair carries, [byte_of_add] shows that byte i of u + v
    equals the sum of byte i of u and byte i of v. *)
Lemma byte_of_add u v i :
  (forall i, 0 <= i < 8 -> byte_of u i + byte_of v i < 256) -> 0 <= i < 8 ->
  byte_of (u + v) i = byte_of u i + byte_of v i.
Proof.
  intros Hb Hi. pose proof (add_low u v i ltac:(lia) Hb) as Hl.
  assert (Hp : 0 < 2 ^ (8 * i)) by (apply Z.pow_pos_nonneg; lia).
  assert (E : (u + v) / 2 ^ (8 * i) = u / 2 ^ (8 * i) + v / 2 ^ (8 * i)).
  { symmetry. apply Z.div_unique with (r := u mod 2 ^ (8 * i) + v mod 2 ^ (8 * i)).
    - left. pose proof (Z.mod_pos_bound u (2 ^ (8 * i)) Hp). pose proof (Z.mod_pos_bound v (2 ^ (8 * i)) Hp). lia.
    - pose proof (Z.div_mod u (2 ^ (8 * i)) ltac:(lia)). pose proof (Z.div_mod v (2 ^ (8 * i)) ltac:(lia)). lia. }
  unfold byte_of at 1. rewrite E, Z.add_mod by lia. fold (byte_of u i) (byte_of v i).
  apply Z.mod_small. pose proof (byte_of_range u i). pose proof (byte_of_range v i). specialize (Hb i Hi). lia.
Qed.

(** When every byte of c below index j is at most the corresponding byte
    of x, [sub_low] proves that no prefix of x - c borrows. *)
Lemma sub_low x c j n : 0 <= n <= j -> j <= 8 ->
  (forall i, 0 <= i < j -> byte_of c i <= byte_of x i) ->
  c mod 2 ^ (8 * n) <= x mod 2 ^ (8 * n).
Proof.
  intros [H0 Hj] H8 Hb. revert Hj. pattern n. apply natlike_ind; [| |exact H0].
  - intros _. rewrite Z.mul_0_r, Z.pow_0_r, !Z.mod_1_r. lia.
  - intros k Hk IH Hj. unfold Z.succ in *. rewrite !low_step by lia.
    assert (Hp : 0 < 2 ^ (8 * k)) by (apply Z.pow_pos_nonneg; lia).
    specialize (IH ltac:(lia)). specialize (Hb k ltac:(lia)). nia.
Qed.

(** When c's bytes below j are at most x's, [byte_of_sub] shows that
    byte i of x - c through index j equals their wrapped byte
    difference. *)
Lemma byte_of_sub x c j i : j <= 8 ->
  (forall i, 0 <= i < j -> byte_of c i <= byte_of x i) -> 0 <= i <= j ->
  byte_of (x - c) i = (byte_of x i - byte_of c i) mod 256.
Proof.
  intros H8 Hb Hi. pose proof (sub_low x c j i ltac:(lia) H8 Hb) as Hl.
  assert (Hp : 0 < 2 ^ (8 * i)) by (apply Z.pow_pos_nonneg; lia).
  assert (E : (x - c) / 2 ^ (8 * i) = x / 2 ^ (8 * i) - c / 2 ^ (8 * i)).
  { symmetry. apply Z.div_unique with (r := x mod 2 ^ (8 * i) - c mod 2 ^ (8 * i)).
    - left. pose proof (Z.mod_pos_bound x (2 ^ (8 * i)) Hp). pose proof (Z.mod_pos_bound c (2 ^ (8 * i)) Hp). lia.
    - pose proof (Z.div_mod x (2 ^ (8 * i)) ltac:(lia)). pose proof (Z.div_mod c (2 ^ (8 * i)) ltac:(lia)). lia. }
  unfold byte_of at 1. rewrite E, Zminus_mod. reflexivity.
Qed.

(** ## Reconstructing a word from bytes

    To check a property of a 64-bit mask by computation, we reconstruct a
    word from its eight bytes and discharge single-byte predicates over
    all 256 possible values. These helpers bridge the gap between
    arbitrary 64-bit words and finite boolean reflection. *)

(** [of_bytes] packs a list of little-endian bytes cs back into an
    integer. *)
Fixpoint of_bytes (cs : list Z) : Z :=
  match cs with [] => 0 | c :: cs => c + 256 * of_bytes cs end.

(** [idx8] lists the eight byte indices of a 64-bit word. *)
Definition idx8 : list Z := [0; 1; 2; 3; 4; 5; 6; 7].

(** Any 64-bit unsigned integer equals [of_bytes] applied to its eight
    bytes, as [of_bytes_byte_of] proves. *)
Lemma of_bytes_byte_of z : 0 <= z < 2 ^ 64 -> of_bytes (map (byte_of z) idx8) = z.
Proof.
  intros Hz. transitivity (z mod 2 ^ (8 * (7 + 1))); [| apply Z.mod_small; exact Hz].
  rewrite low_step by lia. change (8 * 7) with (8 * (6 + 1)).
  rewrite low_step by lia. change (8 * 6) with (8 * (5 + 1)).
  rewrite low_step by lia. change (8 * 5) with (8 * (4 + 1)).
  rewrite low_step by lia. change (8 * 4) with (8 * (3 + 1)).
  rewrite low_step by lia. change (8 * 3) with (8 * (2 + 1)).
  rewrite low_step by lia. change (8 * 2) with (8 * (1 + 1)).
  rewrite low_step by lia. change (8 * 1) with (8 * (0 + 1)).
  rewrite low_step by lia. rewrite Z.mul_0_r, Z.pow_0_r, Z.mod_1_r. cbn [of_bytes map idx8]. lia.
Qed.

(** [idx8_cases] proves that every index between 0 and 7 appears in
    [idx8]. *)
Lemma idx8_cases i : 0 <= i < 8 -> In i idx8.
Proof. intros Hi. cbn. lia. Qed.

(** The tactic [byte_cases] splits a byte index i below 8 into eight
    concrete cases so Rocq can evaluate constant bytes directly. *)
Ltac byte_cases i :=
  let H := fresh in
  assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia;
  repeat destruct H as [H|H]; subst i.

(** [all_bytes] turns a boolean check over `[0..255]` into a universally
    quantified fact about any byte b. *)
Lemma all_bytes (P : Z -> bool) :
  forallb P (map Z.of_nat (seq 0 256)) = true -> forall b, 0 <= b < 256 -> P b = true.
Proof.
  intros H b Hb. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

(** ## The masks

    Glibc uses two different zero-detection formulas because the first
    word may contain garbage before the string starts, whereas loop
    words have no prefix to ignore. Here we mirror the exact 64-bit
    expressions emitted by nanofil and prove what each byte of their
    masks contains. *)

(** [ones7] repeats the byte `0x7f` across all eight bytes of a word. *)
Definition ones7 : Z := 9187201950435737471.
(** [highs] repeats the high-bit mask `0x80` across all eight bytes. *)
Definition highs : Z := 9259542123273814144.
(** [lows] repeats the byte `0x01` across all eight bytes of a word. *)
Definition lows : Z := 72340172838076673.
(** [all64] sets all 64 bits to one (`0xffffffffffffffff`). *)
Definition all64 : Z := 18446744073709551615.

(** [byte_ones7] verifies that every byte of [ones7] equals 127. *)
Lemma byte_ones7 i : 0 <= i < 8 -> byte_of ones7 i = 127.
Proof. intros Hi. byte_cases i; reflexivity. Qed.
(** [byte_highs] verifies that every byte of [highs] equals 128. *)
Lemma byte_highs i : 0 <= i < 8 -> byte_of highs i = 128.
Proof. intros Hi. byte_cases i; reflexivity. Qed.
(** [byte_lows] verifies that every byte of [lows] equals 1. *)
Lemma byte_lows i : 0 <= i < 8 -> byte_of lows i = 1.
Proof. intros Hi. byte_cases i; reflexivity. Qed.
(** [byte_all64] verifies that every byte of [all64] equals 255. *)
Lemma byte_all64 i : 0 <= i < 8 -> byte_of all64 i = 255.
Proof. intros Hi. byte_cases i; reflexivity. Qed.

(** [first_mask] models glibc's `c: find_zero_all` from `c: string-fza.h`
    with every intermediate value wrapped to 64 bits. It marks every
    zero byte in x with 128 and every nonzero byte with 0. *)
Definition first_mask (x : Z) : Z :=
  Z.lxor
    (Z.lor (Z.lor ((Z.land (x mod 2 ^ 64) ones7 mod 2 ^ 64 + ones7) mod 2 ^ 64 mod 2 ^ 64) (x mod 2 ^ 64)
       mod 2 ^ 64) ones7 mod 2 ^ 64)
    all64.

(** [first_mask_on_byte] checks by exhaustive computation that the
    `c: find_zero_all` formula maps byte 0 to 128 and every nonzero byte
    to 0. *)
Lemma first_mask_on_byte b : 0 <= b < 256 ->
  Z.lxor (Z.lor (Z.lor (Z.land b 127 + 127) b) 127) 255 = if b =? 0 then 128 else 0.
Proof.
  intros Hb. apply Z.eqb_eq.
  apply (all_bytes (fun b => Z.lxor (Z.lor (Z.lor (Z.land b 127 + 127) b) 127) 255 =?
                             if b =? 0 then 128 else 0)); [vm_compute; reflexivity | exact Hb].
Qed.

(** Masking any byte with 127 yields a value at most 127, so adding 127
    never overflows a byte, as [land127] verifies. *)
Lemma land127 b : 0 <= b < 256 -> 0 <= Z.land b 127 <= 127.
Proof.
  intros Hb. pose proof (all_bytes (fun b => (0 <=? Z.land b 127) && (Z.land b 127 <=? 127))
    ltac:(vm_compute; reflexivity) b Hb) as H. apply andb_true_iff in H as [H1 H2]. lia.
Qed.

(** [first_mask_byte] lifts [first_mask_on_byte] to a full 64-bit word,
    showing that byte i of [first_mask] is 128 when byte i of x is zero
    and 0 otherwise. *)
Lemma first_mask_byte x i : 0 <= i < 8 -> byte_of (first_mask x) i = if byte_of x i =? 0 then 128 else 0.
Proof.
  intros Hi. unfold first_mask.
  repeat rewrite ?byte_of_mod64, ?byte_of_lxor, ?byte_of_lor, ?byte_all64, ?byte_ones7 by lia.
  rewrite byte_of_add by
    (lia || (intros j Hj; rewrite byte_of_mod64, byte_of_land, byte_of_mod64, byte_ones7 by lia;
             pose proof (land127 (byte_of x j) (byte_of_range x j)); lia)).
  rewrite byte_of_mod64, byte_of_land, byte_of_mod64, byte_ones7 by lia.
  apply first_mask_on_byte, byte_of_range.
Qed.

(** [loop_mask] models glibc's `c: find_zero_low` from `c: string-fzb.h`
    with 64-bit wrapping. Because subtraction can borrow across bytes,
    the mask is only exact up through the first zero byte of x. *)
Definition loop_mask (x : Z) : Z :=
  Z.land
    (Z.land ((x mod 2 ^ 64 - lows) mod 2 ^ 64 mod 2 ^ 64) (Z.lxor (x mod 2 ^ 64) all64 mod 2 ^ 64)
       mod 2 ^ 64)
    highs.

(** [loop_mask_on_byte] verifies by computation that `c: find_zero_low`
    evaluates to 0 on every nonzero byte. *)
Lemma loop_mask_on_byte b : 0 < b < 256 -> Z.land (Z.land ((b - 1) mod 256) (Z.lxor b 255)) 128 = 0.
Proof.
  intros Hb. apply Z.eqb_eq.
  pose proof (all_bytes (fun b => (b =? 0) || (Z.land (Z.land ((b - 1) mod 256) (Z.lxor b 255)) 128 =? 0))
    ltac:(vm_compute; reflexivity) b ltac:(lia)) as H.
  apply orb_true_iff in H as [H|H]; [apply Z.eqb_eq in H; lia | exact H].
Qed.

(** When every byte of x below j is nonzero, subtracting [lows] does not
    borrow through byte j, so [loop_mask_byte'] reduces byte i of
    [loop_mask] to the single-byte formula. *)
Lemma loop_mask_byte' x j i : j <= 8 -> (forall i, 0 <= i < j -> byte_of x i <> 0) -> 0 <= i <= j -> i < 8 ->
  byte_of (loop_mask x) i = Z.land (Z.land ((byte_of x i - 1) mod 256) (Z.lxor (byte_of x i) 255)) 128.
Proof.
  intros Hj Hnz Hi H8. unfold loop_mask.
  rewrite byte_of_land, byte_highs, !byte_of_mod64, byte_of_land, !byte_of_mod64, byte_of_lxor, byte_of_mod64,
    byte_all64 by lia.
  rewrite (byte_of_sub _ _ j i Hj); [| |lia].
  - rewrite byte_lows, byte_of_mod64 by lia. reflexivity.
  - intros k Hk. rewrite byte_lows, byte_of_mod64 by lia.
    pose proof (byte_of_range x k). specialize (Hnz k Hk). lia.
Qed.

(** Below the first zero byte j of x, [loop_mask_below] proves that
    every byte of [loop_mask] is 0. *)
Lemma loop_mask_below x j i : j <= 8 -> (forall i, 0 <= i < j -> byte_of x i <> 0) -> 0 <= i < j ->
  byte_of (loop_mask x) i = 0.
Proof.
  intros Hj Hnz Hi. rewrite (loop_mask_byte' x j i Hj Hnz) by lia. apply loop_mask_on_byte.
  pose proof (byte_of_range x i). specialize (Hnz i Hi). lia.
Qed.

(** At the first zero byte j of x, [loop_mask_at] proves that byte j of
    [loop_mask] equals 128. *)
Lemma loop_mask_at x j : 0 <= j < 8 -> (forall i, 0 <= i < j -> byte_of x i <> 0) -> byte_of x j = 0 ->
  byte_of (loop_mask x) j = 128.
Proof. intros Hj Hnz Hz. rewrite (loop_mask_byte' x j j ltac:(lia) Hnz) by lia. rewrite Hz. reflexivity. Qed.

(** Because [loop_mask] ends with a bitwise conjunction against [highs],
    every byte of [loop_mask] is either 0 or 128, as [loop_mask_01]
    records. *)
Lemma loop_mask_01 x i : 0 <= i < 8 -> byte_of (loop_mask x) i = 0 \/ byte_of (loop_mask x) i = 128.
Proof.
  intros Hi. unfold loop_mask. rewrite byte_of_land, byte_highs by lia.
  match goal with |- context [Z.land (byte_of ?y i) 128] =>
    pose proof (all_bytes (fun b => (Z.land b 128 =? 0) || (Z.land b 128 =? 128))
      ltac:(vm_compute; reflexivity) (byte_of y i) (byte_of_range y i)) as H end.
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; auto.
Qed.

(** ## Words in range

    The population-count and zero-word lemmas require their 64-bit
    operands to lie in `[0, 2^64)` so that no high bits interfere. These
    two helpers establish that range invariant for bitwise conjunctions
    and prove that a word with eight zero bytes equals zero. *)

(** [bits64] shows that any integer in `[0, 2^64)` has bit n equal to
    false for every n from 64 upward. *)
Lemma bits64 z n : 0 <= z < 2 ^ 64 -> 64 <= n -> Z.testbit z n = false.
Proof. intros Hz Hn. rewrite <- (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. Qed.

(** [land_range] proves that the bitwise conjunction of two 64-bit
    unsigned integers also lies in `[0, 2^64)`. *)
Lemma land_range a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.land a b < 2 ^ 64.
Proof.
  intros Ha Hb. assert (E : Z.land a b mod 2 ^ 64 = Z.land a b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_mod_pow2, Z.land_spec by lia.
    destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. rewrite (bits64 a n Ha E). reflexivity. }
  rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.

(** A 64-bit word whose eight bytes are all zero must equal 0, as
    [zero_word] proves. *)
Lemma zero_word z : 0 <= z < 2 ^ 64 -> (forall i, 0 <= i < 8 -> byte_of z i = 0) -> z = 0.
Proof.
  intros Hz H. rewrite <- (of_bytes_byte_of z Hz). cbn [map idx8].
  rewrite !H by lia. reflexivity.
Qed.

(** ## The population count

    Once a word's mask is nonzero, glibc isolates the lowest set bit
    with `r & -r`, subtracts 1 to form a run of trailing ones, and
    counts those bits with a parallel popcount. For a mask whose bytes
    are 0 or 128, the bit count before the first 128 at byte j is
    always 8 * j + 7, so dividing by 8 yields j. *)

(** [tail] models glibc's inlined `c: index_first` function from
    `c: string-fzi.h` on a 64-bit mask r, with every intermediate
    expression wrapped to 64 bits. *)
Definition tail (r : Z) : Z :=
  let v8 := (- (r mod 2 ^ 64)) mod 2 ^ 64 in
  let v9 := Z.land (r mod 2 ^ 64) (v8 mod 2 ^ 64) in
  let v10 := (v9 mod 2 ^ 64 - 1) mod 2 ^ 64 in
  let v11 := v10 mod 2 ^ 64 / 2 ^ (1 mod 64) in
  let v12 := Z.land (v11 mod 2 ^ 64) 6148914691236517205 in
  let v13 := (v10 mod 2 ^ 64 - v12 mod 2 ^ 64) mod 2 ^ 64 in
  let v14 := Z.land (v13 mod 2 ^ 64) 3689348814741910323 in
  let v15 := v13 mod 2 ^ 64 / 2 ^ (2 mod 64) in
  let v16 := Z.land (v15 mod 2 ^ 64) 3689348814741910323 in
  let v17 := (v14 mod 2 ^ 64 + v16 mod 2 ^ 64) mod 2 ^ 64 in
  let v18 := v17 mod 2 ^ 64 / 2 ^ (4 mod 64) in
  let v19 := (v17 mod 2 ^ 64 + v18 mod 2 ^ 64) mod 2 ^ 64 in
  let v20 := Z.land (v19 mod 2 ^ 64) 1085102592571150095 in
  let v21 := (v20 mod 2 ^ 64 * 72340172838076673) mod 2 ^ 64 in
  v21 mod 2 ^ 64 / 2 ^ (56 mod 64).

(** When every byte of r is 0 or 128 and the first 128 sits at byte j,
    [tail_first] proves by exhaustive case analysis that [tail] returns
    8 * j + 7. *)
Lemma tail_first r j : 0 <= r < 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> byte_of r i = 0 \/ byte_of r i = 128) ->
  0 <= j < 8 -> byte_of r j = 128 -> (forall i, 0 <= i < j -> byte_of r i = 0) ->
  tail r = 8 * j + 7.
Proof.
  intros Hr H01 Hj Hjb Hlow. rewrite <- (of_bytes_byte_of r Hr). cbn [map idx8].
  byte_cases j;
    repeat match goal with
      | |- context [byte_of r ?i] =>
          first [ rewrite (Hlow i) by lia | rewrite Hjb
                | let E := fresh in destruct (H01 i ltac:(lia)) as [E|E]; rewrite E ]
      end;
    vm_compute; reflexivity.
Qed.

(** ## The first word, from the string's start

    Because a string need not start on an 8-byte boundary, glibc masks
    the first aligned word with [first_mask] and then shifts the result
    right to discard any zero bytes that precede the string pointer.
    These final lemmas verify the shift amount, the shifted mask bytes,
    and the alignment mask applied to the pointer. *)

(** [first_shift] shifts [first_mask] right by 8 * (a mod 8) bits,
    moving the byte at the string's starting address a down to byte 0. *)
Definition first_shift (x a : Z) : Z :=
  first_mask x mod 2 ^ 64 / 2 ^ ((Z.land (a mod 2 ^ 64) 7 mod 2 ^ 64 * 8) mod 2 ^ 64 mod 2 ^ 32 mod 64).

(** [first_shift_amount] simplifies the wrapped bit-shift expression for
    any non-negative address a to 8 * (a mod 8). *)
Lemma first_shift_amount a : 0 <= a ->
  (Z.land (a mod 2 ^ 64) 7 mod 2 ^ 64 * 8) mod 2 ^ 64 mod 2 ^ 32 mod 64 = 8 * (a mod 8).
Proof.
  intros Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  assert (E : (a mod 2 ^ 64) mod 8 = a mod 8)
    by (rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | lia | exists (2 ^ 61); reflexivity]).
  rewrite E.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  rewrite (Z.mod_small (a mod 8)), (Z.mod_small (a mod 8 * 8)), (Z.mod_small (a mod 8 * 8)), Z.mod_small; lia.
Qed.

(** Byte i of [first_shift] equals 128 when byte i + a mod 8 lies in
    the first word and holds zero in x, and 0 otherwise, as
    [first_shift_byte] proves. *)
Lemma first_shift_byte x a i : 0 <= a -> 0 <= i ->
  byte_of (first_shift x a) i =
    if i + a mod 8 <? 8 then (if byte_of x (i + a mod 8) =? 0 then 128 else 0) else 0.
Proof.
  intros Ha Hi. pose proof (Z.mod_pos_bound a 8 ltac:(lia)). unfold first_shift.
  rewrite first_shift_amount, byte_of_div by lia.
  destruct (i + a mod 8 <? 8) eqn:E.
  - apply Z.ltb_lt in E. rewrite byte_of_mod64, first_mask_byte by lia. reflexivity.
  - apply Z.ltb_ge in E. apply byte_of_high; [apply Z.mod_pos_bound; lia | exact E].
Qed.

(** [first_shift_range] confirms that [first_shift] always produces a
    64-bit unsigned value in `[0, 2^64)`. *)
Lemma first_shift_range x a : 0 <= first_shift x a < 2 ^ 64.
Proof.
  unfold first_shift. pose proof (Z.mod_pos_bound (first_mask x) (2 ^ 64) ltac:(lia)).
  match goal with |- context [_ / 2 ^ ?e] =>
    assert (0 < 2 ^ e) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]) end.
  split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (first_mask x mod 2 ^ 64)); [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

(** [loop_mask_range] confirms that [loop_mask] always produces a 64-bit
    unsigned value in `[0, 2^64)`. *)
Lemma loop_mask_range x : 0 <= loop_mask x < 2 ^ 64.
Proof. unfold loop_mask. apply land_range; [apply Z.mod_pos_bound; lia | vm_compute; split; congruence]. Qed.

(** To load the aligned word holding address a, glibc clears the low
    three bits with a mask. Lemma [land_align] proves that this bitwise
    conjunction with `~7` equals a - a mod 8. *)
Lemma land_align a : 0 <= a < 2 ^ 64 -> Z.land a (18446744073709551608 mod 2 ^ 64) = a - a mod 8.
Proof.
  intros Ha. change (18446744073709551608 mod 2 ^ 64) with (Z.lxor (Z.ones 64) (Z.ones 3)).
  assert (E : Z.land a (Z.lxor (Z.ones 64) (Z.ones 3)) + Z.land a (Z.ones 3) = a).
  { rewrite Z.add_nocarry_lxor.
    - apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, !Z.land_spec, Z.lxor_spec, !Z.testbit_ones by lia.
      rewrite (proj2 (Z.leb_le 0 n) Hn).
      destruct (Z.testbit a n) eqn:E; [|reflexivity].
      destruct (Z.ltb_spec n 3), (Z.ltb_spec n 64); cbn; try reflexivity; try lia.
      rewrite (bits64 a n Ha ltac:(lia)) in E. discriminate.
    - apply Z.bits_inj'. intros n Hn. rewrite Z.bits_0, !Z.land_spec, Z.lxor_spec, !Z.testbit_ones by lia.
      rewrite (proj2 (Z.leb_le 0 n) Hn).
      destruct (Z.testbit a n), (Z.ltb_spec n 3), (Z.ltb_spec n 64); cbn; try reflexivity; lia. }
  rewrite Z.land_ones in E by lia. change (2 ^ 3) with 8 in E. lia.
Qed.
