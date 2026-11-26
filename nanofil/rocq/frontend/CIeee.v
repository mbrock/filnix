(** IEEE 754 binary32, binary64, and x87 80-bit extended arithmetic using
    arbitrary-precision integers only, rounding to nearest with ties to even.

    Operands and results are unsigned bit patterns, never host floating-point
    numbers. Finite intermediates are exact rational numbers, and [round_ratio]
    is the single rounding boundary for normal numbers, gradual underflow, and
    overflow. This module ports nanofil/src/ieee.pl without host float
    operations or axioms so OCaml extraction and CertiRocq λANF produce the
    same bits on every architecture. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Frontend Require Import CAttrs CLex.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Floating-point formats and bit decoding

    Nanofil supports three IEEE-compatible binary formats: binary32 ([FmtS]),
    binary64 ([FmtD]), and the x86-64 x87 80-bit extended format ([FmtX]),
    which stores the significand's integer bit explicitly in bit 63. *)

(** The floating-point format selector: `s` (binary32), `d` (binary64), or `x`
    (x87 80-bit extended `long double`). *)
Inductive ieee_fmt : Type :=
| FmtS
| FmtD
| FmtX.

(** Binary arithmetic operations supported on IEEE bit patterns. *)
Inductive ieee_binop : Type :=
| IeeeAdd
| IeeeSub
| IeeeMul
| IeeeDiv.

(** Floating-point comparison predicates, matching SSE and C relational
    operators. *)
Inductive ieee_cond : Type :=
| ICEq
| ICNe
| ICLt
| ICLe
| ICGt
| ICGe
| ICOrd
| ICUnord.

(** Decoded value class for an unsigned bit pattern, separating infinities,
    NaNs, and finite binary numbers `sig * 2^exp`. *)
Inductive ieee_decoded : Type :=
| DecInf
| DecNan
| DecFin (sig exp : Z).

(** Format geometry `(frac_bits, exp_bits, bias, explicit_int_bit)`. *)
Definition fmt_params (k : ieee_fmt) : Z * Z * Z * Z :=
  match k with
  | FmtS => (23, 8, 127, 0)
  | FmtD => (52, 11, 1023, 0)
  | FmtX => (63, 15, 16383, 1)
  end.

Definition fmt_frac (k : ieee_fmt) : Z :=
  match k with FmtS => 23 | FmtD => 52 | FmtX => 63 end.

Definition fmt_exp (k : ieee_fmt) : Z :=
  match k with FmtS => 8 | FmtD => 11 | FmtX => 15 end.

Definition fmt_bias (k : ieee_fmt) : Z :=
  match k with FmtS => 127 | FmtD => 1023 | FmtX => 16383 end.

Definition fmt_int_bit (k : ieee_fmt) : Z :=
  match k with FmtS => 0 | FmtD => 0 | FmtX => 1 end.

Definition fmt_exp_shift (k : ieee_fmt) : Z :=
  fmt_frac k + fmt_int_bit k.

(** Decode an unsigned bit pattern [b] in format [k] into its sign bit (`0` or
    `1`) and its value classification. *)
Definition ieee_decode (k : ieee_fmt) (b : Z) : Z * ieee_decoded :=
  let f := fmt_frac k in
  let e := fmt_exp k in
  let bias := fmt_bias k in
  let sh := fmt_exp_shift k in
  let s := Z.shiftr b (sh + e) in
  let m := Z.land b (Z.shiftl 1 f - 1) in
  let x := Z.land (Z.shiftr b sh) (Z.shiftl 1 e - 1) in
  let max_e := Z.shiftl 1 e - 1 in
  if Z.eqb x max_e then
    if Z.eqb m 0 then (s, DecInf) else (s, DecNan)
  else if Z.eqb x 0 then
    let p := 1 - bias - f in
    let sig := Z.land b (Z.shiftl 1 sh - 1) in
    (s, DecFin sig p)
  else
    let n := Z.shiftl 1 f + m in
    let p := x - bias - f in
    (s, DecFin n p).

Definition sign_bits (k : ieee_fmt) (s : Z) : Z :=
  Z.shiftl s (fmt_exp_shift k + fmt_exp k).

Definition ieee_infinity (k : ieee_fmt) (s : Z) : Z :=
  let f := fmt_frac k in
  let e := fmt_exp k in
  let i := fmt_int_bit k in
  let sh := fmt_exp_shift k in
  sign_bits k s + Z.shiftl (Z.shiftl 1 e - 1) sh + Z.shiftl i f.

Definition ieee_quiet (k : ieee_fmt) (a : Z) : Z :=
  Z.lor a (Z.shiftl 1 (fmt_frac k - 1)).

Definition ieee_invalid (k : ieee_fmt) : Z :=
  ieee_quiet k (ieee_infinity k 1).

(** ## Exact integer logarithms, scaling, and ties-to-even rounding

    All rounding goes through [round_ratio], which locates the exact binary
    exponent via [ilog_pos], scales the rational `n / d` to the format's
    significand grid, and applies ties-to-even rounding via [round_even]. *)

(** Compute `floor(log2(n))` for `n > 0` without relying on `Z.log2` so both
    OCaml extraction and CertiRocq λANF lower it onto fast shifts. *)
Fixpoint ilog_hi (fuel : nat) (n acc : Z) : Z * Z :=
  match fuel with
  | O => (n, acc)
  | S f =>
      let hi := Z.shiftr n 64 in
      if Z.eqb hi 0 then (n, acc)
      else ilog_hi f hi (acc + 64)
  end.

Definition ilog_u64 (n : Z) : Z :=
  let '(n1, a1) := let h := Z.shiftr n 32 in if Z.eqb h 0 then (n, 0) else (h, 32) in
  let '(n2, a2) := let h := Z.shiftr n1 16 in if Z.eqb h 0 then (n1, a1) else (h, a1 + 16) in
  let '(n3, a3) := let h := Z.shiftr n2 8 in if Z.eqb h 0 then (n2, a2) else (h, a2 + 8) in
  let '(n4, a4) := let h := Z.shiftr n3 4 in if Z.eqb h 0 then (n3, a3) else (h, a3 + 4) in
  let '(n5, a5) := let h := Z.shiftr n4 2 in if Z.eqb h 0 then (n4, a4) else (h, a4 + 2) in
  let h6 := Z.shiftr n5 1 in
  if Z.eqb h6 0 then a5 else a5 + 1.

Definition ilog (n : Z) : Z :=
  if n <=? 0 then -1
  else
    let '(rem, base) := ilog_hi (Z.to_nat 100000) n 0 in
    base + ilog_u64 rem.

Definition scale_ratio (n d e : Z) : Z * Z :=
  if 0 <=? e then (Z.shiftl n e, d)
  else (n, Z.shiftl d (-e)).

(** Round a positive rational `n / d` to the nearest integer, breaking exact
    halfway ties to the even quotient. *)
Definition round_even (n d : Z) : Z :=
  let q0 := Z.div n d in
  let r := Z.modulo n d in
  let twice := 2 * r in
  if (d <? twice) || (Z.eqb twice d && Z.odd q0) then q0 + 1 else q0.

(** Round the non-negative rational `n / d` with sign [s] into format [k]. *)
Definition round_ratio (k : ieee_fmt) (s n d : Z) : Z :=
  if Z.eqb n 0 then sign_bits k s
  else
    let f := fmt_frac k in
    let bias := fmt_bias k in
    let i := fmt_int_bit k in
    let sh := fmt_exp_shift k in
    let e0 := ilog n - ilog d in
    let '(a0, b0) := scale_ratio n d (-e0) in
    let e := if a0 <? b0 then e0 - 1 else e0 in
    let emin := 1 - bias in
    let step := Z.max e emin - f in
    let '(a, c) := scale_ratio n d (-step) in
    let q := round_even a c in
    let '(q1, e1) :=
      if Z.shiftl 1 (f + 1) <=? q then (Z.shiftr q 1, e + 1)
      else (q, Z.max e emin) in
    if bias <? e1 then ieee_infinity k s
    else
      let '(exp_bits, mant) :=
        if q1 <? Z.shiftl 1 f then (0, q1)
        else (e1 + bias, q1 - Z.shiftl (1 - i) f) in
      sign_bits k s + Z.shiftl exp_bits sh + mant.

Definition finite_ratio (sig exp : Z) : Z * Z :=
  scale_ratio sig 1 exp.

Definition signed_ratio (s sig exp : Z) : Z * Z :=
  let '(a, d) := finite_ratio sig exp in
  ((1 - 2 * s) * a, d).

(** ## Conversions, negation, square root, and binary operations

    These operations match `ieee.pl` bit for bit, including x87's two-NaN
    precedence rule and SSE's quiet-first-NaN rule. *)

(** Convert an arbitrary integer [n] to the nearest format-[k] bit pattern. *)
Definition ieee_from_int (k : ieee_fmt) (n : Z) : Z :=
  let s := if n <? 0 then 1 else 0 in
  let mag := if n <? 0 then -n else n in
  round_ratio k s mag 1.

(** Truncate a finite format-[k] float toward zero; returns `None` for
    infinities and NaNs. *)
Definition ieee_to_int (k : ieee_fmt) (b : Z) : option Z :=
  match ieee_decode k b with
  | (s, DecFin sig exp) =>
      let '(a, d) := finite_ratio sig exp in
      Some ((1 - 2 * s) * Z.div a d)
  | _ => None
  end.

(** Flip the sign bit of [a] in format [k], including NaNs. *)
Definition ieee_neg (k : ieee_fmt) (a : Z) : Z :=
  Z.lxor a (sign_bits k 1).

Fixpoint isqrt_loop (fuel : nat) (m x : Z) : Z :=
  match fuel with
  | O => x
  | S f =>
      let y := Z.div (x + Z.div m x) 2 in
      if x <=? y then x else isqrt_loop f m y
  end.

Definition isqrt (m : Z) : Z :=
  if m <=? 0 then 0
  else
    let x0 := Z.shiftl 1 (Z.div (ilog m) 2 + 1) in
    isqrt_loop (Z.to_nat 200) m x0.

(** IEEE 754 square root in format [k], rounded to nearest, ties to even. *)
Definition ieee_sqrt (k : ieee_fmt) (a : Z) : Z :=
  match ieee_decode k a with
  | (_, DecNan) => ieee_quiet k a
  | (_, DecFin 0 _) => a
  | (1, _) => ieee_invalid k
  | (_, DecInf) => a
  | (_, DecFin n0 p0) =>
      let '(n1, p) :=
        if Z.even p0 then (n0, p0) else (n0 * 2, p0 - 1) in
      let g := fmt_frac k + 5 in
      let m := Z.shiftl n1 (2 * g) in
      let q := isqrt m in
      let '(num, den0) :=
        if Z.eqb (q * q) m then (q, 1) else (2 * q + 1, 2) in
      let h := Z.div p 2 - g in
      let '(num1, den) := scale_ratio num den0 h in
      round_ratio k 0 num1 den
  end.

(** Select between two x87 80-bit NaN operands per Intel SDM vol. 1, 4.8.3.5. *)
Definition x87_nan (a b : Z) : Z :=
  let qa := Z.land (Z.shiftr a 62) 1 in
  let qb := Z.land (Z.shiftr b 62) 1 in
  let mask := Z.shiftl 1 64 - 1 in
  let ma := Z.land a mask in
  let mb := Z.land b mask in
  let w :=
    if qb <? qa then a
    else if qa <? qb then b
    else if ma <? mb then b
    else a in
  ieee_quiet FmtX w.

Definition ieee_add_decoded (k : ieee_fmt) (sa : Z) (ta : ieee_decoded)
  (sb : Z) (tb : ieee_decoded) : Z :=
  match ta, tb with
  | DecInf, DecInf =>
      if negb (Z.eqb sa sb) then ieee_invalid k else ieee_infinity k sa
  | DecInf, _ => ieee_infinity k sa
  | _, DecInf => ieee_infinity k sb
  | DecFin sa_sig sa_exp, DecFin sb_sig sb_exp =>
      let '(a, c) := signed_ratio sa sa_sig sa_exp in
      let '(b, d) := signed_ratio sb sb_sig sb_exp in
      let num := a * d + b * c in
      let den := c * d in
      let s :=
        if num <? 0 then 1
        else if Z.eqb num 0 && Z.eqb sa 1 && Z.eqb sb 1 then 1
        else 0 in
      let mag := if num <? 0 then -num else num in
      round_ratio k s mag den
  | _, _ => ieee_invalid k
  end.

Definition ieee_mul_decoded (k : ieee_fmt) (sa : Z) (ta : ieee_decoded)
  (sb : Z) (tb : ieee_decoded) : Z :=
  let s := Z.lxor sa sb in
  match ta, tb with
  | DecInf, DecFin 0 _ | DecFin 0 _, DecInf => ieee_invalid k
  | DecInf, _ | _, DecInf => ieee_infinity k s
  | DecFin na ea, DecFin nb eb =>
      let '(a, c) := finite_ratio na ea in
      let '(b, d) := finite_ratio nb eb in
      round_ratio k s (a * b) (c * d)
  | _, _ => ieee_invalid k
  end.

Definition ieee_div_decoded (k : ieee_fmt) (sa : Z) (ta : ieee_decoded)
  (sb : Z) (tb : ieee_decoded) : Z :=
  let s := Z.lxor sa sb in
  match ta, tb with
  | DecInf, DecInf | DecFin 0 _, DecFin 0 _ => ieee_invalid k
  | DecInf, _ => ieee_infinity k s
  | _, DecInf => sign_bits k s
  | _, DecFin 0 _ => ieee_infinity k s
  | DecFin na ea, DecFin nb eb =>
      let '(a, c) := finite_ratio na ea in
      let '(b, d) := finite_ratio nb eb in
      round_ratio k s (a * d) (c * b)
  | _, _ => ieee_invalid k
  end.

(** Binary IEEE arithmetic (`add`, `sub`, `mul`, `div`) in format [k]. *)
Definition ieee_binary (k : ieee_fmt) (op : ieee_binop) (a b : Z) : Z :=
  let '(sa, ta) := ieee_decode k a in
  let '(sb, tb) := ieee_decode k b in
  match ta, tb with
  | DecNan, DecNan =>
      match k with
      | FmtX => x87_nan a b
      | _ => ieee_quiet k a
      end
  | DecNan, _ => ieee_quiet k a
  | _, DecNan => ieee_quiet k b
  | _, _ =>
      match op with
      | IeeeAdd => ieee_add_decoded k sa ta sb tb
      | IeeeSub => ieee_add_decoded k sa ta (1 - sb) tb
      | IeeeMul => ieee_mul_decoded k sa ta sb tb
      | IeeeDiv => ieee_div_decoded k sa ta sb tb
      end
  end.

(** Convert [a] from format [from_k] to format [to_k], rounding finite values
    to nearest and preserving aligned NaN payloads. *)
Definition ieee_convert (from_k to_k : ieee_fmt) (a : Z) : Z :=
  let '(s, t) := ieee_decode from_k a in
  match t with
  | DecInf => ieee_infinity to_k s
  | DecNan =>
      let ff := fmt_frac from_k in
      let ft := fmt_frac to_k in
      let payload := Z.land a (Z.shiftl 1 ff - 1) in
      let sh := ft - ff in
      let p := if 0 <=? sh then Z.shiftl payload sh else Z.shiftr payload (-sh) in
      ieee_quiet to_k (Z.lor (ieee_infinity to_k s) p)
  | DecFin sig exp =>
      let '(n, d) := finite_ratio sig exp in
      round_ratio to_k s n d
  end.

(** Compare two format-[k] floats under [cond], returning `1` when true and
    `0` when false. *)
Inductive ieee_ord : Type := IOLt | IOEq | IOGt | IOUnord.

Definition ieee_compare (k : ieee_fmt) (cond : ieee_cond) (a b : Z) : Z :=
  let '(sa, ta) := ieee_decode k a in
  let '(sb, tb) := ieee_decode k b in
  let ord :=
    match ta, tb with
    | DecNan, _ | _, DecNan => IOUnord
    | DecInf, DecInf =>
        match Z.compare sb sa with
        | Lt => IOLt | Eq => IOEq | Gt => IOGt
        end
    | DecInf, _ => if Z.eqb sa 1 then IOLt else IOGt
    | _, DecInf => if Z.eqb sb 1 then IOGt else IOLt
    | DecFin na ea, DecFin nb eb =>
        let '(n, d) := signed_ratio sa na ea in
        let '(m, c) := signed_ratio sb nb eb in
        match Z.compare (n * c) (m * d) with
        | Lt => IOLt | Eq => IOEq | Gt => IOGt
        end
    end in
  let ok :=
    match cond, ord with
    | ICEq, IOEq => true
    | ICNe, IOEq => false
    | ICNe, _ => true
    | ICLt, IOLt => true
    | ICLe, IOLt | ICLe, IOEq => true
    | ICGt, IOGt => true
    | ICGe, IOGt | ICGe, IOEq => true
    | ICOrd, IOUnord => false
    | ICOrd, _ => true
    | ICUnord, IOUnord => true
    | _, _ => false
    end in
  if ok then 1 else 0.

(** ## Literal parsing and exact decimal formatting

    [ieee_parse] parses a decimal or C hexadecimal floating literal (without a
    C type suffix) into an exact rational before rounding once into format [k],
    avoiding double rounding through binary64. *)

Definition ieee_digit_val (base : Z) (c : ascii) : option Z :=
  if is_digit c then
    let v := dec_digit_val c in
    if v <? base then Some v else None
  else if 10 <? base then
    match hex_weight c with
    | Some v => if v <? base then Some v else None
    | None => None
    end
  else None.

Fixpoint take_base_digits (base : Z) (cs : list ascii) (acc : Z) (cnt : Z)
  : Z * Z * list ascii :=
  match cs with
  | c :: rest =>
      match ieee_digit_val base c with
      | Some d => take_base_digits base rest (acc * base + d) (cnt + 1)
      | None => (acc, cnt, cs)
      end
  | [] => (acc, cnt, [])
  end.

Definition parse_opt_sign (cs : list ascii) : Z * list ascii :=
  match cs with
  | c :: rest =>
      if Ascii.eqb c "-"%char then (1, rest)
      else if Ascii.eqb c "+"%char then (0, rest)
      else (0, cs)
  | [] => (0, [])
  end.

Definition parse_exp_val (cs : list ascii) : option (Z * list ascii) :=
  let '(s, rest0) := parse_opt_sign cs in
  let '(n, cnt, rest1) := take_base_digits 10 rest0 0 0 in
  if Z.eqb cnt 0 then None
  else Some ((1 - 2 * s) * n, rest1).

Definition parse_significand (base : Z) (cs : list ascii)
  : option (Z * Z * list ascii) :=
  let '(n0, cnt0, rest0) := take_base_digits base cs 0 0 in
  match rest0 with
  | c :: rest1 =>
      if Ascii.eqb c "."%char then
        let '(n1, cnt1, rest2) := take_base_digits base rest1 n0 0 in
        if Z.eqb (cnt0 + cnt1) 0 then None
        else Some (n1, cnt1, rest2)
      else if Z.eqb cnt0 0 then None
      else Some (n0, 0, rest0)
  | [] =>
      if Z.eqb cnt0 0 then None
      else Some (n0, 0, [])
  end.

Definition parse_ieee_literal (cs : list ascii)
  : option (Z * Z * Z * Z) :=
  let '(s, rest0) := parse_opt_sign cs in
  match rest0 with
  | c0 :: c1 :: rest1 =>
      if Ascii.eqb c0 "0"%char &&
         (Ascii.eqb c1 "x"%char || Ascii.eqb c1 "X"%char) then
        match parse_significand 16 rest1 with
        | Some (n, places, cp :: rest2) =>
            if Ascii.eqb cp "p"%char || Ascii.eqb cp "P"%char then
              match parse_exp_val rest2 with
              | Some (ex, []) => Some (s, n, 2, ex - 4 * places)
              | _ => None
              end
            else None
        | _ => None
        end
      else
        match parse_significand 10 rest0 with
        | Some (n, places, rest2) =>
            match rest2 with
            | [] => Some (s, n, 10, -places)
            | ce :: rest3 =>
                if Ascii.eqb ce "e"%char || Ascii.eqb ce "E"%char then
                  match parse_exp_val rest3 with
                  | Some (ex, []) => Some (s, n, 10, ex - places)
                  | _ => None
                  end
                else None
            end
        | None => None
        end
  | _ =>
      match parse_significand 10 rest0 with
      | Some (n, places, rest2) =>
          match rest2 with
          | [] => Some (s, n, 10, -places)
          | ce :: rest3 =>
              if Ascii.eqb ce "e"%char || Ascii.eqb ce "E"%char then
                match parse_exp_val rest3 with
                | Some (ex, []) => Some (s, n, 10, ex - places)
                | _ => None
                end
              else None
          end
      | None => None
      end
  end.

(** Parse a decimal or hexadecimal floating literal without a C type suffix
    into its nearest format-[k] bit pattern. *)
Definition ieee_parse (k : ieee_fmt) (cs : list ascii) : option Z :=
  match parse_ieee_literal cs with
  | None => None
  | Some (s, n, radix, e) =>
      if Z.eqb n 0 then Some (sign_bits k s)
      else
        let bound := if Z.eqb radix 2 then 20000 else 5500 in
        if bound <? e then Some (ieee_infinity k s)
        else if e <? -bound then
          (* Check whether n * radix^e could still be non-zero in subnormal range. *)
          let approx_log2 := ilog n + (if Z.eqb radix 2 then e else Z.div (e * 3322) 1000) in
          if approx_log2 <? -(fmt_bias k + fmt_frac k + 16) then Some (sign_bits k s)
          else
            let d := Z.pow radix (-e) in
            Some (round_ratio k s n d)
        else
          let '(a, d) :=
            if 0 <=? e then (n * Z.pow radix e, 1)
            else (n, Z.pow radix (-e)) in
          Some (round_ratio k s a d)
  end.

(** Format a finite format-[k] float as an exact terminating decimal string
    `[-]<M>e<P>` matching `ieee.pl`'s `ieee_decimal/3`. Returns `None` for
    infinities and NaNs. *)
Definition ieee_decimal (k : ieee_fmt) (b : Z) : option string :=
  match ieee_decode k b with
  | (s, DecFin n e) =>
      let '(m, p) :=
        if 0 <=? e then (Z.shiftl n e, 0)
        else (n * Z.pow 5 (-e), e) in
      let pref := if Z.eqb s 1 then "-"%string else ""%string in
      Some (pref ++ z_to_string m ++ "e" ++ z_to_string p)%string
  | _ => None
  end.
