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
- Structs and unions with float members pass and return by value as
  SysV classifies their eightbytes (abi-findings.md, *Structs with
  float members*): an eightbyte of only floats and doubles is class `d`
  if it holds a double, `s` for a lone float, and a pair of floats is
  `l` (its bytes) in a generic-only function, as clang's `<2 x float>`.
  A returned `tuple` may then hold `s` and `d` words, which come back
  in XMM0 and XMM1 beside the integer words in RDX and RCX.
- `long double` is x87 extended precision, as in clang (see *x87 long
  double* below).
- Refused with a message: `_Complex`.
- `<math.h>` functions are ordinary calls into libm.

## Backends

- amd64.pl (plain SysV) and filc_amd64.pl (Fil-C): SSE2 code. SysV
  passes floats in xmm0-7 and returns them in xmm0, and a variadic call
  sets %al to the number of vector registers used.
- Fil-C: float words in the fast and generic conventions, the
  signature digits for float and double, and `double` through
  `va_arg`, all checked against the pinned pass and runtime and
  recorded in abi-findings.md.

## x87 long double

C's `long double` on x86-64 is the x87 80-bit extended format: a sign,
a 15-bit exponent with bias 16383, an explicit integer bit and 63
fraction bits, so `LDBL_MANT_DIG` is 64. At the pin clang gives it size
16 and alignment 16, stores its 10 bytes followed by 6 bytes of padding,
checks each load and store as a 10-byte access with 8-byte alignment,
and computes with fldt, fstpt and the x87 stack (abi-findings.md, *x87
long double*).

**Decision: a real 80-bit semantics, as a new class `x`.** The
alternative, holding long double values as `d` and converting at memory,
would print and compare differently from clang wherever the extra 11
significand bits matter. 00204's HFAs are bit patterns `printf("%Lf")`
reads back, `1 + 0x1p-60L != 1`, and `(unsigned long)(long double)
ULONG_MAX` round-trips only with 64 bits. A narrower representation
would make nanofil a different C implementation with the same
`<float.h>`, not a cheaper one. The class is kept as small as the
semantics allow:

- **Class `x`** (filc mode only): a value is its 80 bits as an unsigned
  integer below 2^80, so `const(N)` at x is those bits. An `x` value is
  never a parameter, a result, a call argument, a tuple element or a
  phi (the validator rejects each). Values cross calls and joins
  through memory, so no calling convention, register class or phi copy
  needs an 80-bit case.
- **Ops at x:** `add sub mul div neg copy`, `cmp(Cond, x)` with the
  float conditions, `load(x)` and store width `x` (a 10-byte access,
  8-aligned), `va_arg` at x, and data items `item(x, const(Bits))`
  (10 bytes; the frontend pads with `zero(6)`).
- **Conversions:** `ext(s)` and `ext(d)` to x (exact), `truncx` from x
  to s or d (rounded), `xtosi`/`xtoui` to w or l (truncated toward zero;
  out of range is `ub(float_conversion)`), and `swtof uwtof sltof
  ultof` to x (exact for every 64-bit integer).
- **Interpreter:** ieee.pl has the x format with its explicit integer
  bit; results round to nearest even with full 64-bit precision, the
  x87's default control word on Linux. Of two NaN operands the x87
  keeps a quiet one over a signaling one, then the larger significand,
  then the first, quieted; an invalid operation gives the default NaN
  0xFFFF_C000000000000000. `va_arg` at x takes a 16-byte,
  16-aligned cell and reads its first 10 bytes, as
  `filc_get_next_ptr_bytes_for_va_arg(…, 16, 16)` does.
- **Backend:** each x temporary has a 16-byte frame slot (a `wide`
  pool in frame_slots.pl). Each instruction pushes its operands with
  fldt (a constant goes through the red zone), computes, and pops the
  x87 stack empty again, so no x87 register is live across
  instructions, calls or safepoints and the GC never sees x87 state.
  Truncation uses fisttpll; `xtoui` to l subtracts 2^63 above it, and
  `ultof` adds 2^64 to fildll's result when bit 63 is set, both exact.
- **C frontend:** `ldouble` is a real floating type for the usual
  arithmetic conversions (C11 6.3.1.8p1), literals with an `L` suffix,
  constant folding and static data. A long double crosses a call as
  two `l` words, its 16 bytes, through a 16-byte local that only
  `store(x)` writes, so its padding is zero, which is what clang's
  generic packet holds. A function taking or returning one, or a
  struct or union holding one, is generic-only, and an argument
  holding a long double starts at a 16-aligned packet offset after a
  zero pad word, as clang lays out the generic packet. Calls in either
  direction then meet in the generic convention: clang's fast entry
  (digit 3, on the native stack, returned in ST0) is never used, and a
  clang caller's `pizlonatedFI<Sig>` thunk falls back to the generic
  entry. A `?:` of long doubles joins addresses, not values.

The cost of the generic convention is a call's speed, not its
meaning. Programs that print, compare or store long doubles get
clang's bits. Exported long double functions have no fast signature
alias, unlike clang's, so a `// signatures` progtest leaves them out.

## Order

1. IR workstream, first push: the grammar in ir.pl, the validator,
   qbe_parse/qbe_print (since replaced by ir_text.pl), op_kind and
   ieee.pl. The other two build on it.
2. Then, in parallel: the interpreter's float semantics (IR
   workstream), the backends, and the C frontend.
3. Then Lua: `lua -e`, its test suite, and a nix check like
   nix/hello.nix and nix/zlib.nix.
