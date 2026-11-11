(** A floating-point model must reproduce the target machine's results
    without relying on the host machine's floating-point arithmetic or rounding environment.
    This module computes IEEE 754 operations using integers and exact
    ratios, following ieee.pl for binary32, binary64, and x87 extended precision.
    Operands and results remain unsigned bit patterns, with rounding to
    nearest and ties resolved toward the result whose low bit is even.

    Finite values decode into an integer significand and a power of
    two, allowing arithmetic to proceed without intermediate host-float rounding.
    The function [round_ratio] converts exact ratios back to bit
    patterns, handling gradual underflow, significand carry, and overflow to infinity.
    Special-value handling preserves signed zeros and follows the
    target's NaN selection rules, including the different x87 rule for two NaNs.
    Decimal parsing and printing belong to the frontend and are not
    part of the arithmetic model defined here. *)

From Stdlib Require Import ZArith Bool.
Open Scope Z_scope.

(** ## Formats

    Each supported format stores a sign, an exponent, and a significand,
    but their field widths and integer-bit conventions differ.
    The following constants describe those layouts so arithmetic and
    conversion can share one implementation rather than duplicate each format's rules. *)

(** The supported formats use [fmt] to distinguish binary32, binary64,
    and the x87 80-bit extended representation with its explicit integer bit. *)
Inductive fmt : Type := FmtS | FmtD | FmtX.

(** The fraction-field width comes from [frac_bits], excluding the
    integer bit that binary32 and binary64 imply but x87 stores explicitly. *)
Definition frac_bits (k : fmt) : Z := match k with FmtS => 23 | FmtD => 52 | FmtX => 63 end.
(** The exponent-field width comes from [exp_bits], which determines
    both its largest encoded value and the position of the sign bit. *)
Definition exp_bits (k : fmt) : Z := match k with FmtS => 8 | FmtD => 11 | FmtX => 15 end.
(** A normal value's stored exponent includes [bias], the format's
    offset that makes the encoding of one use this exponent-field value. *)
Definition bias (k : fmt) : Z := match k with FmtS => 127 | FmtD => 1023 | FmtX => 16383 end.

(** Only x87 reserves an explicit integer-bit position, so [integer_bit]
    contributes one layout bit there and zero in the other formats. *)
Definition integer_bit (k : fmt) : Z := match k with FmtX => 1 | _ => 0 end.

(** Locating the exponent field uses [exponent_shift], which counts the
    fraction bits and any explicit integer bit beneath its lowest position. *)
Definition exponent_shift (k : fmt) : Z := frac_bits k + integer_bit k.

(** ## Decoding

    Arithmetic first separates a bit pattern's sign from its magnitude
    and identifies infinities and NaNs before computing an ordinary result.
    Finite magnitudes become exact integer-and-exponent pairs, including
    subnormal values and zero, so later operations need no host floats. *)

(** A decoded magnitude uses [fclass] to distinguish infinity, NaN, and
    a finite integer significand multiplied by a power of two. *)
Inductive fclass : Type :=
| Inf (* This constructor represents an infinite magnitude. *)
| NaN (* This constructor represents a not-a-number value. *)
| Finite (n p : Z). (* This constructor represents n multiplied by two to the power p. *)

(** Splitting a stored pattern uses [decode] to return its sign and
    magnitude, treating a zero exponent as a subnormal value or zero.
    For that zero-exponent case, all bits below the exponent contribute
    to the significand rather than receiving an implied leading one. *)
Definition decode (k : fmt) (b : Z) : Z * fclass :=
  let f := frac_bits k in
  let e := exp_bits k in
  let sh := exponent_shift k in
  let s := Z.shiftr b (sh + e) in
  let m := Z.land b (2 ^ f - 1) in
  let x := Z.land (Z.shiftr b sh) (2 ^ e - 1) in
  let t :=
    if x =? 2 ^ e - 1 then (if m =? 0 then Inf else NaN)
    else if x =? 0 then Finite (Z.land b (2 ^ sh - 1)) (1 - bias k - f)
    else Finite (2 ^ f + m) (x - bias k - f) in
  (s, t).

(** A pattern containing only its sign bit comes from [sign_bits],
    which also supplies the positive or negative zero encoding for that sign. *)
Definition sign_bits (k : fmt) (s : Z) : Z := Z.shiftl s (exponent_shift k + exp_bits k).

(** Constructing an infinity uses [infinity] to combine the requested
    sign with the maximal exponent and x87's explicit integer bit where required. *)
Definition infinity (k : fmt) (s : Z) : Z :=
  sign_bits k s + Z.shiftl (2 ^ exp_bits k - 1) (exponent_shift k)
  + Z.shiftl (integer_bit k) (frac_bits k).

(** Quieting a NaN uses [quiet] to set the top fraction bit while
    preserving the sign and the remaining payload bits. *)
Definition quiet (k : fmt) (a : Z) : Z := Z.lor a (2 ^ (frac_bits k - 1)).

(** An invalid arithmetic operation returns the default quiet negative
    NaN, which [invalid] constructs from the format's negative infinity encoding. *)
Definition invalid (k : fmt) : Z := quiet k (infinity k 1).

(** ## Rounding

    Exact arithmetic can produce a ratio between representable values,
    requiring a single rounding decision when the result is encoded.
    These functions choose the nearest result with ties to even,
    including the smaller spacing of subnormals and overflow into infinity. *)

(** Estimating a positive magnitude's exponent uses [ilog], which
    returns its floor base-two logarithm and uses negative one for nonpositive inputs. *)
Definition ilog (n : Z) : Z := if n <=? 0 then -1 else Z.log2 n.

(** Multiplying a ratio by a power of two uses [scale], which shifts
    the numerator for nonnegative exponents and the denominator for negative exponents. *)
Definition scale (n d e : Z) : Z * Z :=
  if 0 <=? e then (Z.shiftl n e, d) else (n, Z.shiftl d (- e)).

(** Rounding a nonnegative ratio to an integer uses [round_even], which
    compares twice the remainder with the denominator to detect a midpoint.
    At a tie, it increments an odd quotient and retains an even one;
    integer division uses the efficient extracted division operation. *)
Definition round_even (n d : Z) : Z :=
  let q0 := n / d in
  let twice := 2 * (n mod d) in
  if (d <? twice) || ((twice =? d) && (q0 mod 2 =? 1)) then q0 + 1 else q0.

(** Encoding a nonnegative ratio uses [round_ratio] to select the
    nearest pattern of the requested format and separately supplied sign.
    Small values use subnormal spacing, a rounding carry adjusts the
    exponent, and a result beyond the largest exponent becomes infinity. *)
Definition round_ratio (k : fmt) (s n d : Z) : Z :=
  if n =? 0 then sign_bits k s else
  let f := frac_bits k in
  let e0 := ilog n - ilog d in
  let '(a0, b0) := scale n d (- e0) in
  let e := if a0 <? b0 then e0 - 1 else e0 in
  let emin := 1 - bias k in
  let step := Z.max e emin - f in
  let '(a, c) := scale n d (- step) in
  let q := round_even a c in
  let '(q1, e1) := if 2 ^ (f + 1) <=? q then (Z.shiftr q 1, e + 1)
                   else (q, Z.max e emin) in
  if bias k <? e1 then infinity k s
  else
    let '(exp, mant) := if q1 <? 2 ^ f then (0, q1)
                        else (e1 + bias k, q1 - Z.shiftl (1 - integer_bit k) f) in
    sign_bits k s + Z.shiftl exp (exponent_shift k) + mant.

(** Turning a finite magnitude into an exact ratio uses [finite_ratio],
    which scales its integer significand by the recorded power of two. *)
Definition finite_ratio (n p : Z) : Z * Z := scale n 1 p.

(** A finite value's signed ratio comes from [signed_ratio], which
    applies the separately decoded sign to the numerator and leaves the denominator positive. *)
Definition signed_ratio (s n p : Z) : Z * Z :=
  let '(a, d) := finite_ratio n p in ((1 - 2 * s) * a, d).

(** ## Integers

    Conversion from an integer rounds only if the floating-point
    format cannot represent the source integer exactly.
    Conversion back truncates finite values toward zero and returns
    no integer for an infinity or a NaN. *)

(** Encoding an integer uses [ieee_from_int] to separate its sign and
    round its absolute magnitude to the nearest pattern of the requested format. *)
Definition ieee_from_int (k : fmt) (n : Z) : Z :=
  round_ratio k (if n <? 0 then 1 else 0) (Z.abs n) 1.

(** Decoding a finite pattern into an integer uses [ieee_to_int], which
    divides the unsigned magnitude before restoring its sign to truncate toward zero.
    Infinities and NaNs produce no integer result, leaving callers to
    handle those cases rather than inventing a numeric conversion. *)
Definition ieee_to_int (k : fmt) (b : Z) : option Z :=
  match decode k b with
  | (s, Finite n p) => let '(a, d) := finite_ratio n p in Some ((1 - 2 * s) * (a / d))
  | _ => None
  end.

(** ## Arithmetic

    Ordinary arithmetic operates on exact decoded values before
    rounding, but zeros, infinities, and NaNs require separate target-specific cases.
    The following functions implement those cases and preserve the
    required sign or NaN payload when an operation chooses an existing special value. *)

(** Negating a pattern uses [ieee_neg] to flip its sign bit directly,
    including signed zeros, infinities, and NaNs without changing their other bits. *)
Definition ieee_neg (k : fmt) (a : Z) : Z := Z.lxor a (sign_bits k 1).

(** When both x87 operands are NaNs, [x87_nan] prefers a quiet NaN over
    a signaling one, then the larger significand, then the first operand.
    It quiets the selected pattern, following the rule in Intel's
    Software Developer's Manual, volume one, section 4.8.3.5. *)
Definition x87_nan (a b : Z) : Z :=
  let qa := Z.land (Z.shiftr a 62) 1 in
  let qb := Z.land (Z.shiftr b 62) 1 in
  let ma := Z.land a (2 ^ 64 - 1) in
  let mb := Z.land b (2 ^ 64 - 1) in
  let w := if qb <? qa then a else if qa <? qb then b else if ma <? mb then b else a in
  quiet FmtX w.

(** The arithmetic selector [fop] distinguishes addition, subtraction,
    multiplication, and division so they can share format decoding and NaN handling. *)
Inductive fop : Type := FAdd | FSub | FMul | FDiv.

(** Detecting zero uses [is_zero] to inspect the finite significand,
    while the sign remains separate and does not affect this test. *)
Definition is_zero (t : fclass) : bool :=
  match t with Finite 0 _ => true | _ => false end.

(** Detecting an infinite magnitude uses [is_inf], independently of the
    separate sign and without treating any NaN as an infinity. *)
Definition is_inf (t : fclass) : bool := match t with Inf => true | _ => false end.

(** Adding non-NaN values uses [binary_add] to combine exact signed
    ratios, while infinities of opposite signs produce the default NaN.
    An exact zero sum is negative only when both operands are negative,
    preserving the target's signed-zero rule for round-to-nearest addition. *)
Definition binary_add (k : fmt) (sa : Z) (ta : fclass) (sb : Z) (tb : fclass) : Z :=
  match ta, tb with
  | Inf, Inf => if negb (sa =? sb) then invalid k else infinity k sa
  | Inf, _ => infinity k sa
  | _, Inf => infinity k sb
  | Finite na pa, Finite nb pb =>
      let '(a, c) := signed_ratio sa na pa in
      let '(b, d) := signed_ratio sb nb pb in
      let n := a * d + b * c in
      let s := if n <? 0 then 1 else if (n =? 0) && (sa =? 1) && (sb =? 1) then 1 else 0 in
      round_ratio k s (Z.abs n) (c * d)
  | _, _ => invalid k
  end.

(** Arithmetic on decoded non-NaN values uses [binary], which dispatches
    to exact-ratio operations after handling the appropriate zero and infinity cases.
    Multiplying zero by infinity, dividing zero by zero, and dividing
    infinity by infinity return the default NaN rather than a finite result. *)
Definition binary (o : fop) (k : fmt) (sa : Z) (ta : fclass) (sb : Z) (tb : fclass) : Z :=
  let s := Z.lxor sa sb in
  match o with
  | FAdd => binary_add k sa ta sb tb
  | FSub => binary_add k sa ta (1 - sb) tb
  | FMul =>
      if (is_inf ta && is_zero tb) || (is_inf tb && is_zero ta) then invalid k
      else if is_inf ta || is_inf tb then infinity k s
      else match ta, tb with
           | Finite na pa, Finite nb pb =>
               let '(a, c) := finite_ratio na pa in
               let '(b, d) := finite_ratio nb pb in
               round_ratio k s (a * b) (c * d)
           | _, _ => invalid k
           end
  | FDiv =>
      if (is_inf ta && is_inf tb) || (is_zero ta && is_zero tb) then invalid k
      else if is_inf ta then infinity k s
      else if is_inf tb then sign_bits k s
      else if is_zero tb then infinity k s
      else match ta, tb with
           | Finite na pa, Finite nb pb =>
               let '(a, c) := finite_ratio na pa in
               let '(b, d) := finite_ratio nb pb in
               round_ratio k s (a * d) (c * b)
           | _, _ => invalid k
           end
  end.

(** A binary operation on stored patterns uses [ieee_binary] to decode
    both operands and choose NaN handling before ordinary arithmetic.
    Binary32 and binary64 prefer the first NaN when both are NaNs,
    while extended precision uses the separate x87 selection rule. *)
Definition ieee_binary (k : fmt) (o : fop) (a b : Z) : Z :=
  let '(sa, ta) := decode k a in
  let '(sb, tb) := decode k b in
  match ta, tb, k with
  | NaN, NaN, FmtX => x87_nan a b
  | NaN, _, _ => quiet k a
  | _, NaN, _ => quiet k b
  | _, _, _ => binary o k sa ta sb tb
  end.

(** Changing formats uses [ieee_convert] to round finite values to the
    nearest destination pattern and preserve an infinity's sign.
    A NaN keeps as much payload as fits, aligned at the top of the
    destination fraction field, and becomes quiet. *)
Definition ieee_convert (from to : fmt) (a : Z) : Z :=
  match decode from a with
  | (s, Inf) => infinity to s
  | (s, NaN) =>
      let payload := Z.land a (2 ^ frac_bits from - 1) in
      let shift := frac_bits to - frac_bits from in
      let p := if 0 <=? shift then Z.shiftl payload shift else Z.shiftr payload (- shift) in
      quiet to (Z.lor (infinity to s) p)
  | (s, Finite n p) => let '(nn, d) := finite_ratio n p in round_ratio to s nn d
  end.

(** A square root uses [ieee_sqrt] to preserve signed zeros and positive
    infinity, quiet NaNs, and reject other negative values with the default NaN.
    A positive finite value is scaled before taking an integer square
    root, retaining enough extra bits to make the final rounding decision.
    Exact roots use that integer result directly; an inexact root uses
    the midpoint above it before rounding to the requested format. *)
Definition ieee_sqrt (k : fmt) (a : Z) : Z :=
  let '(s, t) := decode k a in
  match t with
  | NaN => quiet k a
  | Finite 0 _ => a
  | Inf => if s =? 1 then invalid k else a
  | Finite n0 p0 =>
      if s =? 1 then invalid k else
      let '(n1, p) := if Z.even p0 then (n0, p0) else (n0 * 2, p0 - 1) in
      let g := frac_bits k + 5 in
      let m := Z.shiftl n1 (2 * g) in
      let q := Z.sqrt m in
      let '(num, den0) := if q * q =? m then (q, 1) else (2 * q + 1, 2) in
      let '(num1, den) := scale num den0 (p / 2 - g) in
      round_ratio k 0 num1 den
  end.

(** ## Comparison

    Floating-point comparison needs an unordered case because a NaN
    does not belong to the ordinary numeric ordering.
    The following functions separate that ordering from the requested
    comparison condition, treating the two signed zeros as equal values. *)

(** A comparison selects its condition through [fcond], covering
    equality, inequality, the four ordered relations, and explicit ordered or unordered tests. *)
Inductive fcond : Type := FEq | FNe | FLt | FLe | FGt | FGe | FOrd | FUnord.

(** Comparing two magnitudes produces [order], which adds an unordered
    case to the ordinary less-than, equal, and greater-than results when either operand is NaN. *)
Inductive order : Type := Below | Same | Above | Unordered.

(** An ordinary integer comparison becomes a floating-point ordering
    through [order_of], which translates its three possible results without producing an unordered case. *)
Definition order_of (c : comparison) : order :=
  match c with Lt => Below | Eq => Same | Gt => Above end.

(** Applying a requested comparison test uses [condition] to interpret
    the ordering, including which tests hold when the operands are unordered. *)
Definition condition (c : fcond) (o : order) : bool :=
  match c, o with
  | FEq, Same => true
  | FNe, (Below | Above | Unordered) => true
  | FLt, Below => true
  | FLe, (Below | Same) => true
  | FGt, Above => true
  | FGe, (Above | Same) => true
  | FOrd, (Below | Same | Above) => true
  | FUnord, Unordered => true
  | _, _ => false
  end.

(** Comparing stored patterns uses [ieee_compare] to return one when
    the requested condition holds and zero otherwise, treating signed zeros equally.
    If either operand is NaN, only inequality and the explicit
    unordered condition hold; all ordinary ordered comparisons return zero. *)
Definition ieee_compare (k : fmt) (c : fcond) (a b : Z) : Z :=
  let '(sa, ta) := decode k a in
  let '(sb, tb) := decode k b in
  let o :=
    match ta, tb with
    | NaN, _ | _, NaN => Unordered
    | Inf, Inf => order_of (Z.compare sb sa)
    | Inf, _ => if sa =? 1 then Below else Above
    | _, Inf => if sb =? 1 then Above else Below
    | Finite na pa, Finite nb pb =>
        let '(n, d) := signed_ratio sa na pa in
        let '(m, e) := signed_ratio sb nb pb in
        order_of (Z.compare (n * e) (m * d))
    end in
  if condition c o then 1 else 0.
