# Floating point (M9)

Goal: compile Lua 5.4 with nanofil alone, matching a filcc-built Lua.
This file is the contract between the three workstreams (IR and
interpreter, backends, C frontend). Change it only with the
orchestrating thread's agreement, as for the rest of ir.pl's grammar.

## IR additions

The IR's floating point started from QBE's floating-point IL (QBE
names are given below for reference); the qbe difftest has since been
retired, and IR text now writes float constants as `c(Bits)` terms.

- **Classes** `s` (IEEE 754 binary32) and `d` (binary64), alongside
  w, l and p. Temps, params, phis, call arguments, and `ret` values may
  have class s or d. `Ret` gains `s | d`. Tuple returns stay l/p.
- **Values.** A float value is its bit pattern. `const(N)` at class s or d
  means the bits N (0 ≤ N < 2^32 or 2^64), so constants, loads and
  stores never need a host float, and IR text writes them as `const(N)`
  too. The rest of this item is history: QBE text wrote float constants
  as `s_1.5` / `d_1.5`, the old parser converted the decimal with correct
  rounding (round half to even), and the old printer emitted text that real
  qbe read back as the same bits. Constants that QBE text cannot spell
  (NaNs, infinities, -0) were printed some other exact way; the IR
  workstream chooses and documents it.
  **Chosen spelling:** unsigned decimal integer bit patterns for NaNs,
  infinities and negative zero, e.g. `2147483648` at s and
  `9223372036854775808` at d for -0. QBE accepts integer constants as
  raw bits at float classes, including in `s`/`d` data items. This keeps
  every NaN payload, sign and signaling bit. Finite values print as
  `s_`/`d_` followed by an exact terminating decimal in exponent notation
  (not necessarily shortest). The parser also accepts C hex-floats.
- **Arithmetic:** `add sub mul div neg copy` at s and d. The integer-only
  ops (`rem urem udiv and or xor sar shr shl`) are invalid at s and d.
- **Comparisons:** `cmp(Cond, K)` with K in s, d and Cond in
  `eq ne le lt ge gt o uo` (QBE `ceqd cned cled cltd cged cgtd cod
  cuod`, and the `s` forms). Result class w. The float conds are valid
  only at s/d; the integer conds (`sle ult` …) only at w/l.
- **Conversions** (QBE names, as op atoms):
  - `ext(s)`: s → d (QBE `exts`), result d.
  - `truncd`: d → s.
  - `stosi stoui dtosi dtoui`: float → integer, result w or l.
  - `swtof uwtof sltof ultof`: integer → float, result s or d.
  - `cast`: bitwise w ↔ s and l ↔ d.
- **Memory:** `load(s)`, `load(d)` (QBE `loads`, `loadd`) and store
  widths `s`, `d` (`stores`, `stored`). Data items `item(s, c(Bits))`
  and `item(d, c(Bits))`.
- Floats are valid in both plain and filc mode. A float is never a
  pointer and carries no capability.
- `op_kind/2` gets kinds for the new ops. The IR workstream picks them
  so the validator and backends can dispatch with one clause per case.
  **Chosen kinds:** `float_convert` for `ext(s)` and `truncd`,
  `float_to_int` for `stosi stoui dtosi dtoui`, `int_to_float` for
  `swtof uwtof sltof ultof`, and `cast` for `cast`. Existing arithmetic
  kinds stay unchanged: `additive`, `alu` (mul/div), `neg`, `copy` and
  `cmp`; dispatch on s/d before their integer implementations.

### Integer-only IEEE helper API

`src/ieee.pl` exports the following concrete relations. Bits are unsigned
integers; K, From and To are s/d. No host float enters these relations.

- `ieee_parse(K, Chars, Bits)`: signed decimal or C hex-float, correctly
  rounded directly to K. Strip any C type suffix before calling.
- `ieee_decimal(K, Bits, Chars)`: exact decimal for finite values
  (including signed zero); fails for NaN/inf.
- `ieee_binary(K, Op, A, B, Result)`: add/sub/mul/div, SSE2 NaN rules.
- `ieee_neg(K, A, Result)`: flip the sign bit, including for NaNs.
- `ieee_compare(K, Cond, A, B, Result)`: the float conditions above,
  Result 0/1, unordered NaNs.
- `ieee_convert(From, To, Bits, Result)`: s/d precision conversion.
- `ieee_from_int(K, Integer, Bits)`: mathematically signed or unsigned
  integer to float, RNE; interpret two's-complement before calling.
- `ieee_to_int(K, Bits, Integer)`: truncate toward zero; fails for
  NaN/inf. The caller must check the destination integer's range and
  convert negative results to two's-complement bits as appropriate.

## Semantics

The interpreter models x86-64 SSE2, so that a returned bit pattern
compares exactly against native code:

- Round to nearest even; no traps; subnormals are not flushed.
- NaN results: x86's rules (the first NaN operand, quieted, else the
  default NaN with the sign bit set: 0xFFC00000 / 0xFFF8000000000000).
- `stosi`/`dtosi`/`stoui`/`dtoui` of a NaN or out-of-range value is
  undefined behaviour (`ub(float_conversion)`), as in C.
- Float arithmetic is concrete only: an unknown float operand raises an
  instantiation error (incomplete, never wrong), like an unknown address.
- Arithmetic is exact on both hosts: do it in integers (a small
  softfloat in `src/ieee.pl`), not with the host's floats, whose NaN,
  -0 and single-precision behaviour differ between SWI and Trealla.
  `ieee.pl` also provides decimal ⇄ bits conversion for the parser,
  printer and the C frontend's constant evaluator.

## C

- `float` and `double`, with C's usual arithmetic conversions, default
  argument promotion of `float` to `double` in variadic calls,
  conversions to and from every integer type, comparisons and `!`/`&&`
  on floats, floating constants (decimal and hex, `f`/`F` suffixes), and
  constant expressions in static initializers, evaluated with ieee.pl.
- Refused with a message: `long double`, `_Complex`, and passing or
  returning by value a struct or union that contains a float (SysV
  classifies those into SSE registers; a later step).
- `<math.h>` functions are ordinary calls into libm.

## Backends

- amd64.pl (plain SysV) and filc_amd64.pl (Fil-C): SSE2 code. SysV
  passes floats in xmm0-7 and returns them in xmm0, and a variadic call
  sets %al to the number of vector registers used.
- Fil-C: float words in the fast and generic conventions, the
  signature digits for float and double, and `double` through
  `va_arg`, all checked against the pinned pass and runtime and
  recorded in abi-findings.md.

## Order

1. IR workstream, first push: the grammar in ir.pl, the validator,
   qbe_parse/qbe_print (since replaced by ir_text.pl), op_kind and
   ieee.pl. The other two build on it.
2. Then, in parallel: the interpreter's float semantics (IR
   workstream), the backends, and the C frontend.
3. Then Lua: `lua -e`, its test suite, and a nix check like
   nix/hello.nix and nix/zlib.nix.
