(** IEEE 754 arithmetic with integers only, transcribed from ieee.pl:
    binary32 (`s`), binary64 (`d`) and the x87 80-bit extended format
    (`x`), rounding to nearest, ties to even.

    Operands and results are unsigned bit patterns, as in interp.pl,
    never host floats. A finite value is an exact rational, and
    `round_ratio` is the one place where rounding happens, gradual
    underflow and overflow included. The decimal parser and printer
    (`ieee_parse/3`, `ieee_decimal/3`) are the frontend's and stay out.

    ## Parts

    | Gallina | ieee.pl |
    |---|---|
    | `fmt`, `frac_bits`, `exp_bits`, `bias`, `integer_bit` | `format/4`, `integer_bit/2` |
    | `decode` | `decode/4` |
    | `round_ratio` | `round_ratio/5` |
    | `ieee_from_int`, `ieee_to_int` | the same |
    | `ieee_neg`, `ieee_binary`, `ieee_convert`, `ieee_compare` | the same | *)

From Stdlib Require Import ZArith Bool.
Open Scope Z_scope.

(** ## Formats *)

(** The three float formats, ieee.pl's K: binary32 ([FmtS], `s`),
    binary64 ([FmtD], `d`) and x87 extended ([FmtX], `x`). *)
Inductive fmt : Type := FmtS | FmtD | FmtX.

(** As `format(K, Fraction, _, _)`: the bits of the fraction of the
    format k, without the integer bit, which only x stores
    explicitly. *)
Definition frac_bits (k : fmt) : Z := match k with FmtS => 23 | FmtD => 52 | FmtX => 63 end.
(** As `format(K, _, Exponent, _)`: the bits of the exponent field. *)
Definition exp_bits (k : fmt) : Z := match k with FmtS => 8 | FmtD => 11 | FmtX => 15 end.
(** As `format(K, _, _, Bias)`: the exponent bias, the stored exponent
    of 1.0. *)
Definition bias (k : fmt) : Z := match k with FmtS => 127 | FmtD => 1023 | FmtX => 16383 end.

(** As `integer_bit(K, Bits)`: the explicit integer bit, if any; the
    exponent starts above it. *)
Definition integer_bit (k : fmt) : Z := match k with FmtX => 1 | _ => 0 end.

(** As `exponent_shift(K, Sh)`: the position of the exponent field's
    lowest bit, above the fraction and the integer bit. *)
Definition exponent_shift (k : fmt) : Z := frac_bits k + integer_bit k.

(** ## Decoding *)

(** What a bit pattern is, `decode/4`'s T. *)
Inductive fclass : Type :=
| Inf (* an infinity *)
| NaN (* not a number *)
| Finite (n p : Z). (* the finite value n × 2^p *)

(** As `decode(K, B, S, T)`: the sign S and the value T of the pattern
    b in the format k. A zero exponent is a subnormal (or zero), whose
    significand is all the bits below the exponent. *)
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

(** As `sign_bits(K, S, B)`: the pattern with only the sign s, 0 or 1;
    also the zero of that sign. *)
Definition sign_bits (k : fmt) (s : Z) : Z := Z.shiftl s (exponent_shift k + exp_bits k).

(** As `infinity(K, S, B)`: the infinity of sign s (x's has its
    integer bit set). *)
Definition infinity (k : fmt) (s : Z) : Z :=
  sign_bits k s + Z.shiftl (2 ^ exp_bits k - 1) (exponent_shift k)
  + Z.shiftl (integer_bit k) (frac_bits k).

(** As `quiet(K, A, B)`: the pattern a with the top fraction bit set,
    which makes a NaN quiet. *)
Definition quiet (k : fmt) (a : Z) : Z := Z.lor a (2 ^ (frac_bits k - 1)).

(** As `invalid(K, B)`: the default NaN, a quiet negative one, the
    result of an invalid operation. *)
Definition invalid (k : fmt) : Z := quiet k (infinity k 1).

(** ## Rounding *)

(** As `ilog(N, L)`: floor(log2(N)) for a positive n, and -1 for 0. *)
Definition ilog (n : Z) : Z := if n <=? 0 then -1 else Z.log2 n.

(** As `scale(N, D, E, A, B)`: the ratio A/B that is n/d × 2^e, both
    parts integers. *)
Definition scale (n d e : Z) : Z * Z :=
  if 0 <=? e then (Z.shiftl n e, d) else (n, Z.shiftl d (- e)).

(** As `round_even(N, D, Q)`: the positive quotient N/D rounded to
    nearest, a tie to the even neighbour. N and D are positive, so
    Prolog's `//` is `Z.div` (`Z.quot` is the same here, but its
    extraction divides bit by bit, which takes minutes on the 16000-bit
    ratios of an x denormal). *)
Definition round_even (n d : Z) : Z :=
  let q0 := n / d in
  let twice := 2 * (n mod d) in
  if (d <? twice) || ((twice =? d) && (q0 mod 2 =? 1)) then q0 + 1 else q0.

(** As `round_ratio(K, S, N, D, B)`: the pattern of format k and sign s
    nearest n/d, for n ≥ 0, ties to even. The exponent is the one of
    n/d, raised to the least normal one (so small values round as
    subnormals), and an overflow is an infinity. *)
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

(** As `finite_ratio(T, A, B)`: the finite value n × 2^p as a ratio of
    non-negative integers. *)
Definition finite_ratio (n p : Z) : Z * Z := scale n 1 p.

(** As `signed_ratio(S, T, N, D)`: the same ratio, with the sign s
    applied to its numerator. *)
Definition signed_ratio (s n p : Z) : Z * Z :=
  let '(a, d) := finite_ratio n p in ((1 - 2 * s) * a, d).

(** ## Integers *)

(** As `ieee_from_int(K, N, B)`: the pattern of format k nearest the
    integer n. *)
Definition ieee_from_int (k : fmt) (n : Z) : Z :=
  round_ratio k (if n <? 0 then 1 else 0) (Z.abs n) 1.

(** As `ieee_to_int(K, B, N)`: the finite pattern b truncated toward
    zero; none for an infinity or NaN. The ratio's parts are
    non-negative, so `//` is `Z.div` here too. *)
Definition ieee_to_int (k : fmt) (b : Z) : option Z :=
  match decode k b with
  | (s, Finite n p) => let '(a, d) := finite_ratio n p in Some ((1 - 2 * s) * (a / d))
  | _ => None
  end.

(** ## Arithmetic *)

(** As `ieee_neg(K, A, B)`: the pattern a with its sign bit flipped,
    NaNs included. *)
Definition ieee_neg (k : fmt) (a : Z) : Z := Z.lxor a (sign_bits k 1).

(** As `x87_nan(A, B, R)`: the result of an x op on two NaNs a and b,
    by the x87's rule (Intel SDM vol. 1, 4.8.3.5): a quiet one wins
    over a signaling one, else the one with the larger significand,
    else the first, and the winner is quieted. *)
Definition x87_nan (a b : Z) : Z :=
  let qa := Z.land (Z.shiftr a 62) 1 in
  let qb := Z.land (Z.shiftr b 62) 1 in
  let ma := Z.land a (2 ^ 64 - 1) in
  let mb := Z.land b (2 ^ 64 - 1) in
  let w := if qb <? qa then a else if qa <? qb then b else if ma <? mb then b else a in
  quiet FmtX w.

(** The four arithmetic operations: add, subtract, multiply, divide. *)
Inductive fop : Type := FAdd | FSub | FMul | FDiv.

(** Whether a decoded value t is a zero, of either sign. *)
Definition is_zero (t : fclass) : bool :=
  match t with Finite 0 _ => true | _ => false end.

(** Whether a decoded value t is an infinity. *)
Definition is_inf (t : fclass) : bool := match t with Inf => true | _ => false end.

(** As `binary(add, K, SA, TA, SB, TB, R)`: the sum of two non-NaN
    values, ta of sign sa and tb of sign sb. An exact zero sum is
    negative only when both operands are; infinities of opposite signs
    give the default NaN. *)
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

(** As `binary(Op, K, SA, TA, SB, TB, R)`: the op o on two non-NaN
    values. The invalid cases, zero times infinity, zero over zero and
    infinity over infinity, give the default NaN [invalid]. *)
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

(** As `ieee_binary(K, Op, A, B, R)`: the op o on the patterns a and b
    of format k. A NaN operand gives that NaN quieted, the first if
    both are, as x86's SSE does ([x87_nan] for x); otherwise [binary]
    on the values. *)
Definition ieee_binary (k : fmt) (o : fop) (a b : Z) : Z :=
  let '(sa, ta) := decode k a in
  let '(sb, tb) := decode k b in
  match ta, tb, k with
  | NaN, NaN, FmtX => x87_nan a b
  | NaN, _, _ => quiet k a
  | _, NaN, _ => quiet k b
  | _, _, _ => binary o k sa ta sb tb
  end.

(** As `ieee_convert(From, To, A, B)`: the pattern a of format from in
    the format to, rounded to nearest; a NaN keeps as much of its
    payload as fits, aligned at the top, and is quieted. *)
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

(** ## Comparison *)

(** A float comparison's condition (`condition/2`): equal, not equal,
    the four orders, ordered (neither is a NaN) and unordered (one
    is). *)
Inductive fcond : Type := FEq | FNe | FLt | FLe | FGt | FGe | FOrd | FUnord.

(** How two values compare: the standard order, or unordered when one
    is a NaN. *)
Inductive order : Type := Below | Same | Above | Unordered.

(** The order of a Rocq [comparison]. *)
Definition order_of (c : comparison) : order :=
  match c with Lt => Below | Eq => Same | Gt => Above end.

(** As `condition(Cond, Order)`: whether the condition c holds of two
    values that compare as o. *)
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

(** As `ieee_compare(K, Cond, A, B, R)`: 1 when a c b holds of the
    patterns a and b of format k, else 0. With a NaN only `ne` and
    `uo` hold; the two zeros are equal. *)
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
