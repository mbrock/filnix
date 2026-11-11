(** glibc's fast string functions inspect eight bytes at once by loading
    a 64-bit word and applying arithmetic masks. This module proves
    that those masks find the first zero byte, and extends the result
    to searches for any byte value.

    The proofs use [byte_of] to read one byte of an integer in
    little-endian order, starting with the least significant byte.
    Bitwise operations act independently on each byte, but addition
    and subtraction need bounds that prevent unwanted carries or
    borrows. These facts let the proofs reduce word-wide operations to
    small claims about individual bytes.

    A string may begin partway through the first loaded word, so the
    search must ignore any zero bytes before its start. The first mask
    therefore marks every zero byte exactly, while later masks need
    only identify the first zero byte correctly.

    Counting the bits below the first marker then gives the matching
    byte's position without inspecting each byte in turn. An exclusive-or
    turns searches for other characters into the same zero-byte
    problem, and exhaustive computation checks the remaining byte-sized
    cases. *)

From Stdlib Require Import ZArith Lia List Bool.
From Nanofil Require Import Memory.
Import ListNotations.
Open Scope Z_scope.

(** ## Bytes of a word

    A word-wide mask is easier to understand when each byte can be
    considered separately. The following facts connect byte extraction
    to bit positions, bitwise operations, shifts, and truncation to
    64 bits. *)

(** Extracting byte i moves its eight bits down without changing their
    values, as [byte_of_bits] states for each bit position. *)
Lemma byte_of_bits x i n : 0 <= i -> 0 <= n ->
  Z.testbit (byte_of x i) n = (n <? 8) && Z.testbit x (n + 8 * i).
Proof.
  intros Hi Hn. unfold byte_of. change 256 with (2 ^ 8).
  rewrite Z.testbit_mod_pow2 by lia. rewrite <- Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftr_spec by lia. reflexivity.
Qed.

(** Applying bitwise and to whole words gives the same byte as applying
    it to their corresponding bytes, as [byte_of_land] states. *)
Lemma byte_of_land x y i : 0 <= i -> byte_of (Z.land x y) i = Z.land (byte_of x i) (byte_of y i).
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, !byte_of_bits, Z.land_spec by lia. destruct (n <? 8); reflexivity.
Qed.

(** Applying bitwise or to whole words gives the same byte as applying
    it to their corresponding bytes, as [byte_of_lor] states. *)
Lemma byte_of_lor x y i : 0 <= i -> byte_of (Z.lor x y) i = Z.lor (byte_of x i) (byte_of y i).
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lor_spec, !byte_of_bits, Z.lor_spec by lia. destruct (n <? 8); reflexivity.
Qed.

(** Applying exclusive-or to whole words gives the same byte as applying
    it to their corresponding bytes, as [byte_of_lxor] states. *)
Lemma byte_of_lxor x y i : 0 <= i -> byte_of (Z.lxor x y) i = Z.lxor (byte_of x i) (byte_of y i).
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, !byte_of_bits, Z.lxor_spec by lia. destruct (n <? 8); reflexivity.
Qed.

(** Truncating an integer to 64 bits preserves its eight low bytes,
    which [byte_of_mod64] lets later mask proofs use independently. *)
Lemma byte_of_mod64 z i : 0 <= i < 8 -> byte_of (z mod 2 ^ 64) i = byte_of z i.
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn.
  rewrite !byte_of_bits, Z.testbit_mod_pow2 by lia.
  destruct (n <? 8) eqn:E; [|reflexivity]. apply Z.ltb_lt in E.
  replace (n + 8 * i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(** Dividing by a power of 256 shifts whole bytes toward the low end,
    as [byte_of_div] states for nonnegative byte indices. *)
Lemma byte_of_div z k i : 0 <= k -> 0 <= i -> byte_of (z / 2 ^ (8 * k)) i = byte_of z (i + k).
Proof.
  intros Hk Hi. unfold byte_of. rewrite Z.div_div by (apply Z.pow_nonzero || apply Z.pow_pos_nonneg; lia).
  rewrite <- Z.pow_add_r by lia. do 3 f_equal. lia.
Qed.

(** An unsigned 64-bit value has only eight possibly nonzero bytes, so
    [byte_of_high] gives zero at every higher byte index. *)
Lemma byte_of_high z i : 0 <= z < 2 ^ 64 -> 8 <= i -> byte_of z i = 0.
Proof.
  intros Hz Hi. unfold byte_of. rewrite Z.div_small; [reflexivity|].
  split; [lia|]. apply (Z.lt_le_trans _ (2 ^ 64)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(** Extracting a byte always gives an integer between zero and 255,
    which [byte_of_range] establishes without restrictions on the source
    integer. *)
Lemma byte_of_range z i : 0 <= byte_of z i < 256.
Proof. unfold byte_of. apply Z.mod_pos_bound. lia. Qed.

(** The lemma [low_step] reconstructs the low n + 1 bytes from the
    low n bytes and the next byte at its proper weight. *)
Lemma low_step z n : 0 <= n ->
  z mod 2 ^ (8 * (n + 1)) = z mod 2 ^ (8 * n) + 2 ^ (8 * n) * byte_of z n.
Proof.
  intros Hn. replace (2 ^ (8 * (n + 1))) with (2 ^ (8 * n) * 256)
    by (rewrite Z.mul_add_distr_l, Z.pow_add_r by lia; reflexivity).
  rewrite Z.rem_mul_r by (lia || (pose proof (Z.pow_pos_nonneg 2 (8 * n)); lia)). reflexivity.
Qed.

(** ## Sums and differences byte by byte

    Arithmetic on a word can carry or borrow across byte boundaries,
    unlike the bitwise operations above. The following bounds rule out
    those interactions so that mask proofs can reason about one byte
    at a time. *)

(** If every corresponding byte pair sums below 256, [add_low] shows
    that no low-byte prefix produces a carry into the next byte. *)
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

(** When all byte sums fit without carries, [byte_of_add] identifies
    each byte of the word sum with its corresponding byte sum. *)
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

(** If each subtracted byte below j fits its corresponding source
    byte, [sub_low] shows that no prefix through j needs a borrow. *)
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

(** Without borrows from lower bytes, [byte_of_sub] computes each byte
    through j by subtracting its corresponding bytes and wrapping the
    result to eight bits. *)
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

(** ## Reconstructing words from bytes

    Once a proof knows all eight bytes, it can recover the whole
    unsigned word. The following definitions perform that reconstruction
    and support exhaustive checks of byte indices and byte values. *)

(** The function [of_bytes] builds an integer from a little-endian
    byte list, giving each successive byte a weight 256 times larger. *)
Fixpoint of_bytes (cs : list Z) : Z :=
  match cs with [] => 0 | c :: cs => c + 256 * of_bytes cs end.

(** The list [idx8] enumerates the eight byte positions of a 64-bit
    word, starting with its least significant byte at position zero. *)
Definition idx8 : list Z := [0; 1; 2; 3; 4; 5; 6; 7].

(** Rebuilding an unsigned 64-bit value from its eight extracted bytes
    gives the original integer, as [of_bytes_byte_of] proves. *)
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

(** Every valid byte index of a 64-bit word occurs in [idx8], as
    [idx8_cases] establishes for exhaustive proofs over those positions. *)
Lemma idx8_cases i : 0 <= i < 8 -> In i idx8.
Proof. intros Hi. cbn. lia. Qed.

(** The tactic [byte_cases] splits a valid byte index into its eight
    possible values so that concrete mask bytes can be computed. *)
Ltac byte_cases i :=
  let H := fresh in
  assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia;
  repeat destruct H as [H|H]; subst i.

(** A Boolean property checked on all 256 byte values holds for any
    byte, as [all_bytes] states for exhaustive computational proofs. *)
Lemma all_bytes (P : Z -> bool) :
  forallb P (map Z.of_nat (seq 0 256)) = true -> forall b, 0 <= b < 256 -> P b = true.
Proof.
  intros H b Hb. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

(** ## The masks

    glibc tests several bytes at once by repeating small constants
    across a 64-bit word. The following definitions reproduce its two
    zero-byte masks and prove which output bytes mark a match. *)

(** The constant [ones7] puts hexadecimal 7f in every byte, selecting
    the low seven bits while leaving each byte's high bit clear. *)
Definition ones7 : Z := 9187201950435737471.
(** The constant [highs] puts hexadecimal 80 in every byte, selecting
    each byte's high bit as the marker for a matching position. *)
Definition highs : Z := 9259542123273814144.
(** The constant [lows] puts hexadecimal 01 in every byte, allowing
    word-wide arithmetic to add or subtract one at each byte position. *)
Definition lows : Z := 72340172838076673.
(** The constant [all64] sets all 64 low bits, so exclusive-or with
    this constant complements every bit of an unsigned word. *)
Definition all64 : Z := 18446744073709551615.

(** Every byte of [ones7] equals 127, as [byte_ones7] verifies by
    computing each of the eight possible byte positions. *)
Lemma byte_ones7 i : 0 <= i < 8 -> byte_of ones7 i = 127.
Proof. intros Hi. byte_cases i; reflexivity. Qed.
(** Every byte of [highs] equals 128, as [byte_highs] verifies by
    computing each of the eight possible byte positions. *)
Lemma byte_highs i : 0 <= i < 8 -> byte_of highs i = 128.
Proof. intros Hi. byte_cases i; reflexivity. Qed.
(** Every byte of [lows] equals one, as [byte_lows] verifies by
    computing each of the eight possible byte positions. *)
Lemma byte_lows i : 0 <= i < 8 -> byte_of lows i = 1.
Proof. intros Hi. byte_cases i; reflexivity. Qed.
(** Every byte of [all64] equals 255, as [byte_all64] verifies by
    computing each of the eight possible byte positions. *)
Lemma byte_all64 i : 0 <= i < 8 -> byte_of all64 i = 255.
Proof. intros Hi. byte_cases i; reflexivity. Qed.

(** The first mask must distinguish every zero byte, including matches
    before the string's starting position that will later be discarded.
    The function [first_mask] follows glibc's `c: find_zero_all` with
    the 64-bit wraps emitted by nanofil's IR. *)
Definition first_mask (x : Z) : Z :=
  Z.lxor
    (Z.lor (Z.lor ((Z.land (x mod 2 ^ 64) ones7 mod 2 ^ 64 + ones7) mod 2 ^ 64 mod 2 ^ 64) (x mod 2 ^ 64)
       mod 2 ^ 64) ones7 mod 2 ^ 64)
    all64.

(** On a single byte, [first_mask_on_byte] shows that the first mask's
    arithmetic returns 128 for zero and zero for every other value. *)
Lemma first_mask_on_byte b : 0 <= b < 256 ->
  Z.lxor (Z.lor (Z.lor (Z.land b 127 + 127) b) 127) 255 = if b =? 0 then 128 else 0.
Proof.
  intros Hb. apply Z.eqb_eq.
  apply (all_bytes (fun b => Z.lxor (Z.lor (Z.lor (Z.land b 127 + 127) b) 127) 255 =?
                             if b =? 0 then 128 else 0)); [vm_compute; reflexivity | exact Hb].
Qed.

(** Selecting a byte's low seven bits gives at most 127, as [land127]
    proves so that adding another 127 cannot carry into the next byte. *)
Lemma land127 b : 0 <= b < 256 -> 0 <= Z.land b 127 <= 127.
Proof.
  intros Hb. pose proof (all_bytes (fun b => (0 <=? Z.land b 127) && (Z.land b 127 <=? 127))
    ltac:(vm_compute; reflexivity) b Hb) as H. apply andb_true_iff in H as [H1 H2]. lia.
Qed.

(** At each valid position, [first_mask_byte] shows that the word-wide
    mask marks exactly the zero bytes with 128 and clears the others. *)
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

(** Later loop iterations need only locate the first zero byte, so
    they use glibc's cheaper `c: find_zero_low` calculation. The function
    [loop_mask] reproduces it with the IR's wraps; higher bytes may
    contain extra markers after the first match. *)
Definition loop_mask (x : Z) : Z :=
  Z.land
    (Z.land ((x mod 2 ^ 64 - lows) mod 2 ^ 64 mod 2 ^ 64) (Z.lxor (x mod 2 ^ 64) all64 mod 2 ^ 64)
       mod 2 ^ 64)
    highs.

(** On a nonzero byte without an incoming borrow, [loop_mask_on_byte]
    shows that the loop mask's arithmetic clears the result to zero. *)
Lemma loop_mask_on_byte b : 0 < b < 256 -> Z.land (Z.land ((b - 1) mod 256) (Z.lxor b 255)) 128 = 0.
Proof.
  intros Hb. apply Z.eqb_eq.
  pose proof (all_bytes (fun b => (b =? 0) || (Z.land (Z.land ((b - 1) mod 256) (Z.lxor b 255)) 128 =? 0))
    ltac:(vm_compute; reflexivity) b ltac:(lia)) as H.
  apply orb_true_iff in H as [H|H]; [apply Z.eqb_eq in H; lia | exact H].
Qed.

(** When every source byte below j is nonzero, subtracting the repeated
    one cannot borrow into any byte through j. Under that condition,
    [loop_mask_byte'] reduces each output byte to the corresponding
    single-byte calculation. *)
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

(** Every position before the first zero byte has a clear mask byte,
    as [loop_mask_below] proves from the absence of borrows. *)
Lemma loop_mask_below x j i : j <= 8 -> (forall i, 0 <= i < j -> byte_of x i <> 0) -> 0 <= i < j ->
  byte_of (loop_mask x) i = 0.
Proof.
  intros Hj Hnz Hi. rewrite (loop_mask_byte' x j i Hj Hnz) by lia. apply loop_mask_on_byte.
  pose proof (byte_of_range x i). specialize (Hnz i Hi). lia.
Qed.

(** The first zero byte receives a marker of 128, as [loop_mask_at]
    proves when all preceding source bytes are nonzero. *)
Lemma loop_mask_at x j : 0 <= j < 8 -> (forall i, 0 <= i < j -> byte_of x i <> 0) -> byte_of x j = 0 ->
  byte_of (loop_mask x) j = 128.
Proof. intros Hj Hnz Hz. rewrite (loop_mask_byte' x j j ltac:(lia) Hnz) by lia. rewrite Hz. reflexivity. Qed.

(** Regardless of the source bytes, [loop_mask_01] shows that each
    output byte is either zero or the marker value 128. *)
Lemma loop_mask_01 x i : 0 <= i < 8 -> byte_of (loop_mask x) i = 0 \/ byte_of (loop_mask x) i = 128.
Proof.
  intros Hi. unfold loop_mask. rewrite byte_of_land, byte_highs by lia.
  match goal with |- context [Z.land (byte_of ?y i) 128] =>
    pose proof (all_bytes (fun b => (Z.land b 128 =? 0) || (Z.land b 128 =? 128))
      ltac:(vm_compute; reflexivity) (byte_of y i) (byte_of_range y i)) as H end.
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; auto.
Qed.

(** ## Words in range

    The mask proofs use unbounded Rocq integers to describe fixed-width
    machine operations. The following bounds keep those descriptions
    within 64 bits and let byte-wise equality determine the whole word. *)

(** An unsigned 64-bit value has no set bits above position 63, which
    [bits64] establishes for reasoning about whole-word masks. *)
Lemma bits64 z n : 0 <= z < 2 ^ 64 -> 64 <= n -> Z.testbit z n = false.
Proof. intros Hz Hn. rewrite <- (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. Qed.

(** Applying bitwise and to unsigned 64-bit values cannot set a higher
    bit, so [land_range] keeps the result in the same range. *)
Lemma land_range a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.land a b < 2 ^ 64.
Proof.
  intros Ha Hb. assert (E : Z.land a b mod 2 ^ 64 = Z.land a b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_mod_pow2, Z.land_spec by lia.
    destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. rewrite (bits64 a n Ha E). reflexivity. }
  rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.

(** If every byte of an unsigned 64-bit value is zero, [zero_word]
    concludes that the whole integer is zero as well. *)
Lemma zero_word z : 0 <= z < 2 ^ 64 -> (forall i, 0 <= i < 8 -> byte_of z i = 0) -> z = 0.
Proof.
  intros Hz H. rewrite <- (of_bytes_byte_of z Hz). cbn [map idx8].
  rewrite !H by lia. reflexivity.
Qed.

(** ## The population count

    After a mask marks the matching bytes, glibc must find the first
    marker's byte index. It counts the bits below the lowest set bit
    and divides by eight to obtain that position. *)

(** The function [tail] follows the inlined population count used by
    glibc's `c: index_first`, including each fixed-width wrap. It counts
    the bits below the input mask's lowest set bit rather than the
    set bits of the mask itself. *)
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

(** For a mask whose first marker is at byte j, [tail_first] gives a
    count of eight times j plus seven. Dividing that count by eight
    therefore recovers the byte index, as exhaustive computation proves
    for every nonempty eight-byte marker pattern. *)
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

    A string need not begin at an aligned word address, so the first
    load may include bytes before its start. The following shift
    discards their mask positions while preserving every possible
    match from the string's first byte onward. *)

(** The function [first_shift] shifts the exact first-word mask right
    by the string address's offset within its aligned word. The first
    string byte then occupies mask position zero, and earlier matches
    no longer contribute. *)
Definition first_shift (x a : Z) : Z :=
  first_mask x mod 2 ^ 64 / 2 ^ ((Z.land (a mod 2 ^ 64) 7 mod 2 ^ 64 * 8) mod 2 ^ 64 mod 2 ^ 32 mod 64).

(** The emitted shift expression equals eight times the address's
    byte offset within its word, as [first_shift_amount] proves despite
    the nested wraps. *)
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

(** The lemma [first_shift_byte] identifies each shifted byte with the
    zero test for its original source position, or zero beyond the
    loaded word. *)
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

(** Shifting the first mask cannot leave the unsigned 64-bit range,
    which [first_shift_range] establishes for later population-count
    reasoning. *)
Lemma first_shift_range x a : 0 <= first_shift x a < 2 ^ 64.
Proof.
  unfold first_shift. pose proof (Z.mod_pos_bound (first_mask x) (2 ^ 64) ltac:(lia)).
  match goal with |- context [_ / 2 ^ ?e] =>
    assert (0 < 2 ^ e) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]) end.
  split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (first_mask x mod 2 ^ 64)); [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

(** The loop mask also stays within the unsigned 64-bit range, as
    [loop_mask_range] proves from its final bitwise and operation. *)
Lemma loop_mask_range x : 0 <= loop_mask x < 2 ^ 64.
Proof. unfold loop_mask. apply land_range; [apply Z.mod_pos_bound; lia | vm_compute; split; congruence]. Qed.

(** Clearing an unsigned address's low three bits rounds it down to
    its aligned word, as [land_align] states for the emitted mask. *)
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

(** ## Searching for a byte

    Searching for a particular character can reuse the zero-byte
    machinery after an exclusive-or with that character in every byte.
    The following definitions construct the repeated word and transfer
    the first-match guarantees to this more general search. *)

(** Multiplying a byte by [lows] repeats it across all eight positions,
    which [repeat_byte] uses to follow glibc's `c: repeat_bytes` helper. *)
Definition repeat_byte (c : Z) : Z := c * lows.

(** Every position contains the supplied byte, as [byte_repeat_byte]
    verifies by computing all byte values at each of the eight indices. *)
Lemma byte_repeat_byte c i : 0 <= c < 256 -> 0 <= i < 8 -> byte_of (repeat_byte c) i = c.
Proof.
  intros Hc Hi. apply Z.eqb_eq.
  assert (H : forallb (fun i => forallb (fun c => byte_of (repeat_byte c) i =? c)
    (map Z.of_nat (seq 0 256))) idx8 = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H i (idx8_cases i Hi)).
  exact (all_bytes (fun c => byte_of (repeat_byte c) i =? c) H c Hc).
Qed.

(** Exclusive-or with a repeated byte produces zero exactly at matching
    positions, as [byte_of_lxor_repeat] proves for glibc's character
    searches. *)
Lemma byte_of_lxor_repeat x c i : 0 <= c < 256 -> 0 <= i < 8 ->
  (byte_of (Z.lxor x (repeat_byte c)) i = 0 <-> byte_of x i = c).
Proof.
  intros Hc Hi. rewrite byte_of_lxor, byte_repeat_byte by lia. apply Z.lxor_eq_0_iff.
Qed.

(** When j is the first matching byte, [eq_mask_first] shows that the
    transformed loop mask is clear below j and marked there. The same
    population-count result can therefore locate an arbitrary byte
    rather than only a string's terminating zero. *)
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
