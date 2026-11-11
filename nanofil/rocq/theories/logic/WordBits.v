(** Whole-word byte and bitmask facts, for proofs of glibc's
    word-at-a-time string functions (docs/glibc-ir.md), promoted from
    rocq/glibc/StrlenBits.v, whose strlen proof first needed them.

    glibc's string functions load whole 64-bit words and find a byte in
    each with masks (string-fza.h, string-fzb.h), then its index with a
    population count (string-fzi.h). Each fact is stated over
    [byte_of], the model's little-endian byte i of a word:
    - [byte_of_land], [byte_of_lor], [byte_of_lxor]: bitwise ops work
      on each byte apart; [byte_of_mod64] and [byte_of_div]: the
      model's wrap to 64 bits keeps the low eight bytes, and a shift
      right by whole bytes moves them down;
    - [byte_of_add]: a sum whose bytes do not carry adds byte by byte;
      [byte_of_sub]: a difference with no borrow below byte j
      subtracts byte by byte through byte j;
    - [first_mask_byte]: `find_zero_all`'s mask ([first_mask]) marks
      exactly the zero bytes, with 128 each, and [first_shift_byte]
      moves them down to a string's start in its word;
    - [loop_mask_below] and [loop_mask_at]: `find_zero_low`'s mask
      ([loop_mask]) is 0 below the word's first zero byte and 128 at
      it;
    - [tail_first]: the population count `index_first` inlines
      ([tail]) finds the first 128 of a mask whose bytes are 0 or 128;
    - [byte_of_lxor_repeat] and [eq_mask_first]: a word xor
      [repeat_byte] c is zero exactly where the word's byte is c, so a
      search for c (memchr, strchrnul, strcmp's mismatch) is the zero
      search of that xor.
    Every claim about all bytes is reduced to one about a byte, and the
    byte claims are checked on all 256 bytes by computation. *)

From Stdlib Require Import ZArith Lia List Bool.
From Nanofil Require Import Memory.
Import ListNotations.
Open Scope Z_scope.

(** ## Bytes of a word *)

(** Bit n of byte i of x is bit 8i + n of x, for n below 8. *)
Lemma byte_of_bits x i n : 0 <= i -> 0 <= n ->
  Z.testbit (byte_of x i) n = (n <? 8) && Z.testbit x (n + 8 * i).
Proof.
  intros Hi Hn. unfold byte_of. change 256 with (2 ^ 8).
  rewrite Z.testbit_mod_pow2 by lia. rewrite <- Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftr_spec by lia. reflexivity.
Qed.

(** A byte of a bitwise and is the and of the bytes. *)
Lemma byte_of_land x y i : 0 <= i -> byte_of (Z.land x y) i = Z.land (byte_of x i) (byte_of y i).
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, !byte_of_bits, Z.land_spec by lia. destruct (n <? 8); reflexivity.
Qed.

(** A byte of a bitwise or is the or of the bytes. *)
Lemma byte_of_lor x y i : 0 <= i -> byte_of (Z.lor x y) i = Z.lor (byte_of x i) (byte_of y i).
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lor_spec, !byte_of_bits, Z.lor_spec by lia. destruct (n <? 8); reflexivity.
Qed.

(** A byte of a bitwise xor is the xor of the bytes. *)
Lemma byte_of_lxor x y i : 0 <= i -> byte_of (Z.lxor x y) i = Z.lxor (byte_of x i) (byte_of y i).
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, !byte_of_bits, Z.lxor_spec by lia. destruct (n <? 8); reflexivity.
Qed.

(** The wrap to 64 bits keeps the low eight bytes. *)
Lemma byte_of_mod64 z i : 0 <= i < 8 -> byte_of (z mod 2 ^ 64) i = byte_of z i.
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite !byte_of_bits, Z.testbit_mod_pow2 by lia.
  destruct (n <? 8) eqn:E; [|reflexivity]. apply Z.ltb_lt in E.
  replace (n + 8 * i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(** A shift right by k whole bytes moves byte i + k to byte i. *)
Lemma byte_of_div z k i : 0 <= k -> 0 <= i -> byte_of (z / 2 ^ (8 * k)) i = byte_of z (i + k).
Proof.
  intros Hk Hi. unfold byte_of. rewrite Z.div_div by (apply Z.pow_nonzero || apply Z.pow_pos_nonneg; lia).
  rewrite <- Z.pow_add_r by lia. do 3 f_equal. lia.
Qed.

(** A 64-bit word has no bytes above its eighth. *)
Lemma byte_of_high z i : 0 <= z < 2 ^ 64 -> 8 <= i -> byte_of z i = 0.
Proof.
  intros Hz Hi. unfold byte_of. rewrite Z.div_small; [reflexivity|].
  split; [lia|]. apply (Z.lt_le_trans _ (2 ^ 64)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(** A byte is in [0, 256). *)
Lemma byte_of_range z i : 0 <= byte_of z i < 256.
Proof. unfold byte_of. apply Z.mod_pos_bound. lia. Qed.

(** The low n + 1 bytes are the low n bytes and byte n above them. *)
Lemma low_step z n : 0 <= n ->
  z mod 2 ^ (8 * (n + 1)) = z mod 2 ^ (8 * n) + 2 ^ (8 * n) * byte_of z n.
Proof.
  intros Hn. replace (2 ^ (8 * (n + 1))) with (2 ^ (8 * n) * 256)
    by (rewrite Z.mul_add_distr_l, Z.pow_add_r by lia; reflexivity).
  rewrite Z.rem_mul_r by (lia || (pose proof (Z.pow_pos_nonneg 2 (8 * n)); lia)). reflexivity.
Qed.

(** ## Sums and differences byte by byte *)

(** Where no byte pair of u and v sums past 255, no low part of them
    carries. *)
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

(** A byte of a sum with no carries is the sum of the bytes. *)
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

(** Where c's bytes below j are at most x's, no low part of x - c
    through byte j borrows. *)
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

(** A byte i at or below j of x - c, where c's bytes below j are at
    most x's, is the difference of the bytes, wrapped to a byte. *)
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

(** ## A word from its bytes *)

(** The little-endian integer of the bytes cs. *)
Fixpoint of_bytes (cs : list Z) : Z :=
  match cs with [] => 0 | c :: cs => c + 256 * of_bytes cs end.

(** The eight byte indices of a word. *)
Definition idx8 : list Z := [0; 1; 2; 3; 4; 5; 6; 7].

(** A 64-bit word is the integer of its eight bytes. *)
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

(** Each of the eight byte indices is one of [idx8]'s. *)
Lemma idx8_cases i : 0 <= i < 8 -> In i idx8.
Proof. intros Hi. cbn. lia. Qed.

(** Byte i of a constant, for each i below 8, by computing it. *)
Ltac byte_cases i :=
  let H := fresh in
  assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia;
  repeat destruct H as [H|H]; subst i.

(** A property of bytes, checked by computing it on all 256. *)
Lemma all_bytes (P : Z -> bool) :
  forallb P (map Z.of_nat (seq 0 256)) = true -> forall b, 0 <= b < 256 -> P b = true.
Proof.
  intros H b Hb. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

(** ## The masks *)

(** 0x7f in every byte. *)
Definition ones7 : Z := 9187201950435737471.
(** 0x80 in every byte. *)
Definition highs : Z := 9259542123273814144.
(** 0x01 in every byte. *)
Definition lows : Z := 72340172838076673.
(** All 64 bits. *)
Definition all64 : Z := 18446744073709551615.

(** The bytes of 0x7f in every byte. *)
Lemma byte_ones7 i : 0 <= i < 8 -> byte_of ones7 i = 127.
Proof. intros Hi. byte_cases i; reflexivity. Qed.
(** The bytes of 0x80 in every byte. *)
Lemma byte_highs i : 0 <= i < 8 -> byte_of highs i = 128.
Proof. intros Hi. byte_cases i; reflexivity. Qed.
(** The bytes of 0x01 in every byte. *)
Lemma byte_lows i : 0 <= i < 8 -> byte_of lows i = 1.
Proof. intros Hi. byte_cases i; reflexivity. Qed.
(** The bytes of all 64 bits. *)
Lemma byte_all64 i : 0 <= i < 8 -> byte_of all64 i = 255.
Proof. intros Hi. byte_cases i; reflexivity. Qed.

(** glibc's `find_zero_all` (string-fza.h) on the first word x, as
    nanofil's IR computes it, every read wrapped to 64 bits: 128 in
    each zero byte of x, 0 in each other. *)
Definition first_mask (x : Z) : Z :=
  Z.lxor
    (Z.lor (Z.lor ((Z.land (x mod 2 ^ 64) ones7 mod 2 ^ 64 + ones7) mod 2 ^ 64 mod 2 ^ 64) (x mod 2 ^ 64)
       mod 2 ^ 64) ones7 mod 2 ^ 64)
    all64.

(** The first mask's byte, on one byte. *)
Lemma first_mask_on_byte b : 0 <= b < 256 ->
  Z.lxor (Z.lor (Z.lor (Z.land b 127 + 127) b) 127) 255 = if b =? 0 then 128 else 0.
Proof.
  intros Hb. apply Z.eqb_eq.
  apply (all_bytes (fun b => Z.lxor (Z.lor (Z.lor (Z.land b 127 + 127) b) 127) 255 =?
                             if b =? 0 then 128 else 0)); [vm_compute; reflexivity | exact Hb].
Qed.

(** A byte's low seven bits are at most 127. *)
Lemma land127 b : 0 <= b < 256 -> 0 <= Z.land b 127 <= 127.
Proof.
  intros Hb. pose proof (all_bytes (fun b => (0 <=? Z.land b 127) && (Z.land b 127 <=? 127))
    ltac:(vm_compute; reflexivity) b Hb) as H. apply andb_true_iff in H as [H1 H2]. lia.
Qed.

(** Byte i of the first mask is 128 if byte i of x is zero, else 0. *)
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

(** glibc's `find_zero_low` (string-fzb.h) on a loop word x, as
    nanofil's IR computes it: (x - 0x01...) & ~x & 0x80..., every read
    wrapped. Exact below x's first zero byte, and 128 at it. *)
Definition loop_mask (x : Z) : Z :=
  Z.land
    (Z.land ((x mod 2 ^ 64 - lows) mod 2 ^ 64 mod 2 ^ 64) (Z.lxor (x mod 2 ^ 64) all64 mod 2 ^ 64)
       mod 2 ^ 64)
    highs.

(** The loop mask's byte, on one nonzero byte: 0. *)
Lemma loop_mask_on_byte b : 0 < b < 256 -> Z.land (Z.land ((b - 1) mod 256) (Z.lxor b 255)) 128 = 0.
Proof.
  intros Hb. apply Z.eqb_eq.
  pose proof (all_bytes (fun b => (b =? 0) || (Z.land (Z.land ((b - 1) mod 256) (Z.lxor b 255)) 128 =? 0))
    ltac:(vm_compute; reflexivity) b ltac:(lia)) as H.
  apply orb_true_iff in H as [H|H]; [apply Z.eqb_eq in H; lia | exact H].
Qed.

(** Byte i at or below j of the loop mask, where x's bytes below j are
    nonzero: the loop mask's byte of x's byte i, with no borrow. *)
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

(** Below x's first zero byte j, the loop mask's bytes are 0. *)
Lemma loop_mask_below x j i : j <= 8 -> (forall i, 0 <= i < j -> byte_of x i <> 0) -> 0 <= i < j ->
  byte_of (loop_mask x) i = 0.
Proof.
  intros Hj Hnz Hi. rewrite (loop_mask_byte' x j i Hj Hnz) by lia. apply loop_mask_on_byte.
  pose proof (byte_of_range x i). specialize (Hnz i Hi). lia.
Qed.

(** At x's first zero byte j, the loop mask's byte is 128. *)
Lemma loop_mask_at x j : 0 <= j < 8 -> (forall i, 0 <= i < j -> byte_of x i <> 0) -> byte_of x j = 0 ->
  byte_of (loop_mask x) j = 128.
Proof. intros Hj Hnz Hz. rewrite (loop_mask_byte' x j j ltac:(lia) Hnz) by lia. rewrite Hz. reflexivity. Qed.

(** Every byte of the loop mask is 0 or 128. *)
Lemma loop_mask_01 x i : 0 <= i < 8 -> byte_of (loop_mask x) i = 0 \/ byte_of (loop_mask x) i = 128.
Proof.
  intros Hi. unfold loop_mask. rewrite byte_of_land, byte_highs by lia.
  match goal with |- context [Z.land (byte_of ?y i) 128] =>
    pose proof (all_bytes (fun b => (Z.land b 128 =? 0) || (Z.land b 128 =? 128))
      ltac:(vm_compute; reflexivity) (byte_of y i) (byte_of_range y i)) as H end.
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; auto.
Qed.

(** ## Words in range *)

(** A word in range has no bits from 64 up. *)
Lemma bits64 z n : 0 <= z < 2 ^ 64 -> 64 <= n -> Z.testbit z n = false.
Proof. intros Hz Hn. rewrite <- (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. Qed.

(** An and of words in range is in range. *)
Lemma land_range a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.land a b < 2 ^ 64.
Proof.
  intros Ha Hb. assert (E : Z.land a b mod 2 ^ 64 = Z.land a b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_mod_pow2, Z.land_spec by lia.
    destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. rewrite (bits64 a n Ha E). reflexivity. }
  rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.

(** A word in range whose bytes are all 0 is 0. *)
Lemma zero_word z : 0 <= z < 2 ^ 64 -> (forall i, 0 <= i < 8 -> byte_of z i = 0) -> z = 0.
Proof.
  intros Hz H. rewrite <- (of_bytes_byte_of z Hz). cbn [map idx8].
  rewrite !H by lia. reflexivity.
Qed.

(** ## The population count *)

(** glibc's `index_first` (string-fzi.h) as nanofil inlines it on the
    mask r: the population count of the bits below r's lowest set bit,
    (r & -r) - 1, every read wrapped. *)
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

(** On a mask in range whose bytes are 0 or 128, with the first 128 at
    byte j: the count is 8j + 7, so its eighth is j. Each of the 255
    masks with a first 128 at some byte is computed. *)
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

(** ## The first word, from the string's start *)

(** The first word's mask shifted right by the string's offset k in
    its word, k * 8 bits, as nanofil's IR computes it from the address
    a: the zero bytes of x from byte k on, moved down to byte 0. *)
Definition first_shift (x a : Z) : Z :=
  first_mask x mod 2 ^ 64 / 2 ^ ((Z.land (a mod 2 ^ 64) 7 mod 2 ^ 64 * 8) mod 2 ^ 64 mod 2 ^ 32 mod 64).

(** The shift is the offset of a in its word, in bytes. *)
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

(** Byte i of the shifted mask: 128 where byte i + k of x is zero, for
    i + k inside the word, else 0. *)
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

(** The shifted mask is in range. *)
Lemma first_shift_range x a : 0 <= first_shift x a < 2 ^ 64.
Proof.
  unfold first_shift. pose proof (Z.mod_pos_bound (first_mask x) (2 ^ 64) ltac:(lia)).
  match goal with |- context [_ / 2 ^ ?e] =>
    assert (0 < 2 ^ e) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]) end.
  split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (first_mask x mod 2 ^ 64)); [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

(** The loop mask is in range. *)
Lemma loop_mask_range x : 0 <= loop_mask x < 2 ^ 64.
Proof. unfold loop_mask. apply land_range; [apply Z.mod_pos_bound; lia | vm_compute; split; congruence]. Qed.

(** Rounding a 64-bit address down to its word, as nanofil's IR does
    it: an and with ~7. *)
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

(** ## Searching for a byte *)

(** The byte c in every byte of a word, as glibc's `repeat_bytes`
    (string-misc.h) makes it: c times 0x01 in every byte. *)
Definition repeat_byte (c : Z) : Z := c * lows.

(** Each of the eight bytes of [repeat_byte] c is c, checked for every
    byte at every index by computation. *)
Lemma byte_repeat_byte c i : 0 <= c < 256 -> 0 <= i < 8 -> byte_of (repeat_byte c) i = c.
Proof.
  intros Hc Hi. apply Z.eqb_eq.
  assert (H : forallb (fun i => forallb (fun c => byte_of (repeat_byte c) i =? c)
    (map Z.of_nat (seq 0 256))) idx8 = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H i (idx8_cases i Hi)).
  exact (all_bytes (fun c => byte_of (repeat_byte c) i =? c) H c Hc).
Qed.

(** A byte of x xor [repeat_byte] c is zero exactly where x's byte is
    c: glibc's `find_eq_low` and `find_eq_all` are the zero finders on
    that xor. *)
Lemma byte_of_lxor_repeat x c i : 0 <= c < 256 -> 0 <= i < 8 ->
  (byte_of (Z.lxor x (repeat_byte c)) i = 0 <-> byte_of x i = c).
Proof.
  intros Hc Hi. rewrite byte_of_lxor, byte_repeat_byte by lia. apply Z.lxor_eq_0_iff.
Qed.

(** Where byte j is x's first byte equal to c, the loop mask of x xor
    [repeat_byte] c is 0 below j and 128 at j: [loop_mask_below] and
    [loop_mask_at] for a search for c, whose index [tail_first] then
    finds. *)
Lemma eq_mask_first x c j : 0 <= c < 256 -> 0 <= j < 8 ->
  (forall i, 0 <= i < j -> byte_of x i <> c) -> byte_of x j = c ->
  (forall i, 0 <= i < j -> byte_of (loop_mask (Z.lxor x (repeat_byte c))) i = 0) /\
  byte_of (loop_mask (Z.lxor x (repeat_byte c))) j = 128.
Proof.
  intros Hc Hj Hne Heq.
  assert (Hnz : forall i, 0 <= i < j -> byte_of (Z.lxor x (repeat_byte c)) i <> 0).
  { intros i Hi H. apply (Hne i Hi). apply (byte_of_lxor_repeat x c i Hc); [lia | exact H]. }
  split.
  - intros i Hi. apply (loop_mask_below _ j); [lia | exact Hnz | exact Hi].
  - apply loop_mask_at; [exact Hj | exact Hnz |]. apply byte_of_lxor_repeat; assumption.
Qed.
