(** An x86-64 instruction computes on bit patterns of 8, 16, 32 or 64
    bits, and the processor manual states each result as an unsigned
    or a signed integer of that width. This module gives those
    readings as functions on unbounded integers, so that the
    instruction semantics in Amd64Step.v can quote the manual's
    arithmetic directly.

    The IR model in Ops.v describes integer values the same way, as
    unbounded integers reduced modulo a power of two. The machine
    semantics uses the same representation so that a theorem about
    emitted code can compare the two results without a conversion
    between number systems.

    This module does not mention registers, flags or instructions. It
    is the arithmetic that the rest of the amd64 semantics shares, and
    its lemmas are the facts about wrapping and sign that every later
    proof needs. *)

From Stdlib Require Import ZArith Bool Lia.
Local Open Scope Z_scope.

(** ## Operand sizes

    Every integer instruction acts at one of four operand sizes, which
    the AT&T suffixes `b`, `w`, `l` and `q` name. This section defines
    the sizes and the power of two that bounds the bit patterns of
    each size. *)

(** An operand [size] selects how many low bits of a register an
    instruction reads or writes. *)
Inductive size : Type :=
| S8 (* a byte, suffix `b` *)
| S16 (* a 16-bit word, suffix `w` *)
| S32 (* a 32-bit long, suffix `l` *)
| S64. (* a 64-bit quad, suffix `q` *)

(** The function [size_eqb] decides whether two operand sizes are the
    same. *)
Definition size_eqb (z z' : size) : bool :=
  match z, z' with
  | S8, S8 | S16, S16 | S32, S32 | S64, S64 => true
  | _, _ => false
  end.

(** The function [size_bits] returns the number of bits in an operand
    of the given size. *)
Definition size_bits (z : size) : Z :=
  match z with
  | S8 => 8
  | S16 => 16
  | S32 => 32
  | S64 => 64
  end.

(** The function [size_ltb] decides whether the first size is strictly
    narrower than the second. An extending move requires its source to
    be narrower than its destination. *)
Definition size_ltb (z z' : size) : bool := size_bits z <? size_bits z'.

(** The [size_modulus] of a size is the number of distinct bit patterns
    of that size. Every unsigned value of the size is below it. *)
Definition size_modulus (z : size) : Z := 2 ^ size_bits z.

(** ## Unsigned and signed readings

    The processor stores only bit patterns. An instruction such as
    `div` reads a pattern as an unsigned integer, while `idiv` and the
    overflow flag read the same pattern in two's complement. This
    section defines both readings and the test for whether an integer
    fits the signed range of a size. *)

(** The function [wrap] reduces an integer to the bit pattern that a
    register of the given size keeps of it. The result is the unsigned
    reading of that pattern. *)
Definition wrap (z : size) (x : Z) : Z := x mod size_modulus z.

(** The function [sign_bit] returns the top bit of the pattern that x
    has at the given size. The sign flag copies this bit from a
    result. *)
Definition sign_bit (z : size) (x : Z) : bool := size_modulus z / 2 <=? wrap z x.

(** The function [signed_at] reads the pattern that x has at the given
    size as a two's-complement integer. *)
Definition signed_at (z : size) (x : Z) : Z :=
  if sign_bit z x then wrap z x - size_modulus z else wrap z x.

(** The function [fits_signed] decides whether an integer lies in the
    two's-complement range of a size. The overflow flag reports that
    the exact signed result of an operation does not fit. *)
Definition fits_signed (z : size) (n : Z) : bool :=
  (- (size_modulus z / 2) <=? n) && (n <? size_modulus z / 2).

(** The function [sign_fill] returns the pattern of all ones when x is
    negative at the given size, and zero otherwise. The instructions
    `cltd` and `cqto` write this pattern to the upper half of a
    dividend. *)
Definition sign_fill (z : size) (x : Z) : Z :=
  if sign_bit z x then size_modulus z - 1 else 0.

(** The function [even_parity] reports whether the low byte of x has an
    even number of one bits. The parity flag holds this value after an
    arithmetic instruction. *)
Definition even_parity (x : Z) : bool :=
  negb (xorb (xorb (xorb (Z.testbit x 0) (Z.testbit x 1))
                   (xorb (Z.testbit x 2) (Z.testbit x 3)))
             (xorb (xorb (Z.testbit x 4) (Z.testbit x 5))
                   (xorb (Z.testbit x 6) (Z.testbit x 7)))).

(** ## Double-width division

    The instructions `div` and `idiv` divide a dividend of twice the
    operand size, whose upper half is in `%rdx` and whose lower half
    is in `%rax`. The processor raises a divide error when the divisor
    is zero or when the quotient does not fit the operand size. This
    section states that rule once, apart from any register. *)

(** The function [unsigned_pair] reads two patterns of the given size
    as one unsigned integer of twice the size, with hi as its upper
    half. *)
Definition unsigned_pair (z : size) (hi lo : Z) : Z :=
  wrap z hi * size_modulus z + wrap z lo.

(** The function [signed_pair] reads the same double-width pattern in
    two's complement. *)
Definition signed_pair (z : size) (hi lo : Z) : Z :=
  let m := size_modulus z in
  let u := unsigned_pair z hi lo in
  if m * m / 2 <=? u then u - m * m else u.

(** The function [divide_words] divides the double-width dividend hi:lo
    by the divisor d, signed when sg holds and unsigned otherwise. It
    returns the patterns of the quotient and the remainder, or `None`
    where the processor raises a divide error. A signed division
    truncates toward zero, so its remainder has the sign of the
    dividend. *)
Definition divide_words (sg : bool) (z : size) (hi lo d : Z) : option (Z * Z) :=
  if sg then
    let n := signed_pair z hi lo in
    let dv := signed_at z d in
    if dv =? 0 then None
    else if fits_signed z (Z.quot n dv)
         then Some (wrap z (Z.quot n dv), wrap z (Z.rem n dv))
         else None
  else
    let n := unsigned_pair z hi lo in
    let dv := wrap z d in
    if dv =? 0 then None
    else if n / dv <? size_modulus z
         then Some (n / dv, n mod dv)
         else None.

(** ## Facts about wrapping

    A proof about emitted code repeatedly needs to know that a wrapped
    value is in range, that wrapping twice changes nothing, and that
    wrapping commutes with addition and negation. These lemmas state
    those facts for every operand size. *)

(** Every size has a positive modulus, so reduction modulo it is always
    defined. *)
Lemma size_modulus_pos (z : size) : 0 < size_modulus z.
Proof.
Admitted.

(** The modulus of every size is even, and its half is the weight of
    the sign bit. *)
Lemma size_modulus_half (z : size) : size_modulus z = 2 * (size_modulus z / 2).
Proof.
Admitted.

(** The modulus of every size is at least 256, so small constants such
    as 1 and 16 are valid patterns at every size. *)
Lemma size_modulus_ge (z : size) : 256 <= size_modulus z.
Proof.
Admitted.

(** A wrapped value is a valid unsigned pattern of its size. *)
Lemma wrap_range (z : size) (x : Z) : 0 <= wrap z x < size_modulus z.
Proof.
Admitted.

(** Wrapping leaves a valid unsigned pattern unchanged. *)
Lemma wrap_small (z : size) (x : Z) :
  0 <= x < size_modulus z -> wrap z x = x.
Proof.
Admitted.

(** Wrapping a second time at the same size changes nothing. *)
Lemma wrap_wrap (z : size) (x : Z) : wrap z (wrap z x) = wrap z x.
Proof.
Admitted.

(** A pattern of a narrower size is already a valid pattern of a wider
    size. *)
Lemma wrap_wider (z z' : size) (x : Z) :
  size_bits z <= size_bits z' -> wrap z' (wrap z x) = wrap z x.
Proof.
Admitted.

(** Truncating to a narrower size discards an earlier truncation to a
    wider size. *)
Lemma wrap_narrower (z z' : size) (x : Z) :
  size_bits z <= size_bits z' -> wrap z (wrap z' x) = wrap z x.
Proof.
Admitted.

(** Wrapping an operand before an addition does not change the wrapped
    sum. *)
Lemma wrap_add_l (z : size) (x y : Z) : wrap z (wrap z x + y) = wrap z (x + y).
Proof.
Admitted.

(** The same holds for the right operand of an addition. *)
Lemma wrap_add_r (z : size) (x y : Z) : wrap z (x + wrap z y) = wrap z (x + y).
Proof.
Admitted.

(** Wrapping the left operand before a subtraction does not change the
    wrapped difference. *)
Lemma wrap_sub_l (z : size) (x y : Z) : wrap z (wrap z x - y) = wrap z (x - y).
Proof.
Admitted.

(** The same holds for the right operand of a subtraction. *)
Lemma wrap_sub_r (z : size) (x y : Z) : wrap z (x - wrap z y) = wrap z (x - y).
Proof.
Admitted.

(** Wrapping an operand before a negation does not change the wrapped
    negation. *)
Lemma wrap_opp (z : size) (x : Z) : wrap z (- wrap z x) = wrap z (- x).
Proof.
Admitted.

(** Adding a multiple of the modulus does not change a wrapped value. *)
Lemma wrap_add_modulus (z : size) (x k : Z) :
  wrap z (x + k * size_modulus z) = wrap z x.
Proof.
Admitted.

(** A wrapped value is zero exactly when the modulus divides the
    integer. For a valid pattern this means that the pattern is zero. *)
Lemma wrap_zero_small (z : size) (x : Z) :
  0 <= x < size_modulus z -> (wrap z x =? 0) = (x =? 0).
Proof.
Admitted.

(** ## Facts about the signed reading

    The signed reading and the unsigned reading of one pattern differ
    by the modulus when the sign bit is set. These lemmas let a proof
    move between the two readings, which the division theorem does for
    every operand. *)

(** The signed reading of any integer lies in the two's-complement
    range of the size. *)
Lemma signed_at_range (z : size) (x : Z) :
  - (size_modulus z / 2) <= signed_at z x < size_modulus z / 2.
Proof.
Admitted.

(** The signed reading therefore always passes the range test. *)
Lemma signed_at_fits (z : size) (x : Z) : fits_signed z (signed_at z x) = true.
Proof.
Admitted.

(** The signed reading depends only on the pattern, so wrapping first
    changes nothing. *)
Lemma signed_at_wrap (z : size) (x : Z) : signed_at z (wrap z x) = signed_at z x.
Proof.
Admitted.

(** The signed reading and the original integer have the same
    pattern. *)
Lemma wrap_signed_at (z : size) (x : Z) : wrap z (signed_at z x) = wrap z x.
Proof.
Admitted.

(** An integer in the signed range is recovered from its pattern. *)
Lemma signed_at_of_fits (z : size) (n : Z) :
  fits_signed z n = true -> signed_at z (wrap z n) = n.
Proof.
Admitted.

(** The signed reading is zero exactly when the pattern is zero. *)
Lemma signed_at_zero (z : size) (x : Z) :
  (signed_at z x =? 0) = (wrap z x =? 0).
Proof.
Admitted.

(** The signed reading is -1 exactly when the pattern is all ones. *)
Lemma signed_at_minus_one (z : size) (x : Z) :
  (signed_at z x =? -1) = (wrap z x =? size_modulus z - 1).
Proof.
Admitted.

(** The range test unfolds to the two inequalities it checks. *)
Lemma fits_signed_iff (z : size) (n : Z) :
  fits_signed z n = true <-> - (size_modulus z / 2) <= n < size_modulus z / 2.
Proof.
Admitted.

(** ## Facts about masks

    The emitted division code selects between two values without a
    branch. It builds a mask that is zero or all ones and combines the
    mask with an operand by `and` and `xor`. These lemmas give the
    arithmetic meaning of those bitwise operations on valid patterns. *)

(** A bitwise `and` of two valid patterns is a valid pattern. *)
Lemma land_range (z : size) (x y : Z) :
  0 <= x < size_modulus z -> 0 <= y < size_modulus z ->
  0 <= Z.land x y < size_modulus z.
Proof.
Admitted.

(** A bitwise `or` of two valid patterns is a valid pattern. *)
Lemma lor_range (z : size) (x y : Z) :
  0 <= x < size_modulus z -> 0 <= y < size_modulus z ->
  0 <= Z.lor x y < size_modulus z.
Proof.
Admitted.

(** A bitwise `xor` of two valid patterns is a valid pattern. *)
Lemma lxor_range (z : size) (x y : Z) :
  0 <= x < size_modulus z -> 0 <= y < size_modulus z ->
  0 <= Z.lxor x y < size_modulus z.
Proof.
Admitted.

(** An `and` with the all-ones mask keeps a valid pattern. *)
Lemma land_ones (z : size) (x : Z) :
  0 <= x < size_modulus z -> Z.land x (size_modulus z - 1) = x.
Proof.
Admitted.

(** An `xor` with the all-ones mask complements a valid pattern, which
    in arithmetic subtracts it from the mask. *)
Lemma lxor_ones (z : size) (x : Z) :
  0 <= x < size_modulus z ->
  Z.lxor x (size_modulus z - 1) = size_modulus z - 1 - x.
Proof.
Admitted.

(** ## Facts about the double-width dividend

    Before a signed division, `cltd` or `cqto` fills the upper half of
    the dividend with copies of the sign bit of the lower half. Before
    an unsigned division, the emitted code clears the upper half.
    These lemmas show that both preparations make the double-width
    dividend equal to the single-width operand. *)

(** A lower half extended by its own sign reads, as a signed double
    word, as the signed reading of the lower half alone. *)
Lemma signed_pair_fill (z : size) (x : Z) :
  signed_pair z (sign_fill z x) x = signed_at z x.
Proof.
Admitted.

(** A lower half under a zero upper half reads, as an unsigned double
    word, as the unsigned reading of the lower half alone. *)
Lemma unsigned_pair_zero (z : size) (x : Z) :
  unsigned_pair z 0 x = wrap z x.
Proof.
Admitted.

(** The sign fill of any integer is a valid pattern. *)
Lemma sign_fill_range (z : size) (x : Z) :
  0 <= sign_fill z x < size_modulus z.
Proof.
Admitted.
