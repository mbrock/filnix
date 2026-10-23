# Floating point (M9)

Goal: compile Lua 5.4 with nanofil alone, matching a filcc-built Lua.
This file is the contract between the three workstreams (IR and
interpreter, backends, C frontend). Change it only with the
orchestrating thread's agreement, as for the rest of ir.pl's grammar.

## IR additions

The IR follows QBE's floating-point IL, so plain modules with floats
still difftest against real qbe.

- **Classes** `s` (IEEE 754 binary32) and `d` (binary64), alongside
  w, l and p. Temps, params, phis, call arguments, and `ret` values may
  have class s or d. `Ret` gains `s | d`. Tuple returns stay l/p.
- **Values.** A float value is its bit pattern. `c(N)` at class s or d
  means the bits N (0 ≤ N < 2^32 or 2^64), so constants, loads and
  stores never need a host float. QBE text writes float constants as
  `s_1.5` / `d_1.5`: the parser converts the decimal with correct
  rounding (round half to even), and the printer emits text that real
  qbe reads back as the same bits. Constants that QBE text cannot spell
  (NaNs, infinities, -0) are printed some other exact way; the IR
  workstream chooses and documents it.
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
   qbe_parse/qbe_print, op_kind and ieee.pl. The other two build on it.
2. Then, in parallel: the interpreter's float semantics (IR
   workstream), the backends, and the C frontend.
3. Then Lua: `lua -e`, its test suite, and a nix check like
   nix/hello.nix and nix/zlib.nix.
