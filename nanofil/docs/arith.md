# One arithmetic, three readings

nanofil computes C integer arithmetic in three places: `c_types`'
`const_eval/4` folds constant expressions over the typed tree, the IR
interpreter runs what `c_lower` emits for them, and clang (Fil-C's,
`FILCC`) has its own reading as compiler of record. This page records a
cross-check of the three over generated well-typed expressions, the
domain where they must agree, how they differ outside it, and the bugs
it found. It is the campaign's research direction of the same name
([campaign.md](campaign.md#further-semantic-investigations)).

## Method

[`tests/arith.pl`](../tests/arith.pl) generates expressions over the
twelve integer types (`_Bool` to `unsigned long long`): leaves are
boundary values of each type (0, 1, -1, maximum, minimum) written as a
cast of a literal, plus shift counts; operators are the unary `- + ~ !`,
every binary operator of `c_parse:c_operator/4` (arithmetic, shifts,
comparisons, bitwise, `&&`, `||`), `?:` and casts. A tree's type comes
from `c_types`' own relations: `form/4` asks `binary_operands/6`,
`unary_operand/3` and `usual_arith_conversion/3`, so the space is the one
the elaborator types. It is a relation, so the operators are enumerated
by running it with the tree unbound. The type relations themselves run
forwards only (they commit with cuts), so the generator enumerates
operand types and asks for the result type, not the other way round.

Each expression is printed once, fully parenthesized, and that text is
read five ways:

| Reading | What it is |
|---|---|
| `const` | `const_eval/4` on the parsed text: a value, `ub`, or not constant. The elaborated type must be the generator's. |
| `ir` | the interpreter on `T g(void) { return E; }` lowered by `c_lower` |
| `ir_params` | the same with every leaf a parameter, so the IR performs the conversions that lowering folds for literal operands |
| `ice` | clang `-std=c11 -pedantic-errors` accepts `_Static_assert((E) \|\| 1, "")`: E is an integer constant expression to clang |
| `fold` | clang's value of E as a static initializer in its default mode, which folds with warnings, read from the emitted data; `none` when clang refuses |

The return type is `long long`, or `unsigned long long` for a 64-bit
unsigned E, which keeps every value (C11 6.8.6.4p3); the static
initializer uses the same type.

## The overlap, stated

`agreement/2` in the script is the statement, one class per case:

| Class | Readings | Means |
|---|---|---|
| `overlap` | `ice`, and then `const = ir = fold` | clang accepts an ICE: all three agree on the value |
| `fold_extension` | not `ice`, `const = ir = fold` | nanofil folds what pedantic clang rejects, to clang's GNU-folded value and the IR's |
| `rejected(traps)` | not `ice`, `const` ub or not constant, `ir` ub | division by zero or `MIN / -1`: undefined (6.5.5p5-6), and the IR traps |
| `rejected(wraps_as_clang)` | not `ice`, `const` not a value, `ir = fold` | undefined; the IR's wrapped or masked value happens to be clang's |
| `rejected(differs)` | not `ice`, `const` not a value, `ir ≠ fold` | undefined; IR and clang fold differently |

Anything else is a bug and fails the run. Two rules carry the weight:

1. **Where clang sees a constant, all three agree.** No expression in
   the overlap may fold to a different value, fail to fold, or run
   differently.
2. **nanofil folds only what its IR computes.** If `const_eval` gives a
   value, the IR gives the same value and clang folds it to the same
   value, whether or not C11 calls it a constant. `ir` and `ir_params`
   always agree.

Outside the overlap the readings differ deliberately:

- **Constant rejection vs. IR wrapping.** A shift count that is negative
  or not below the promoted width (6.5.7p3), division by zero (6.5.5p5)
  and `MIN / -1` or `MIN % -1` (6.5.5p6) make `const_eval` give `ub`, so
  `_Static_assert`, `case`, array sizes and static initializers refuse
  them. The IR is defined there: it masks the shift count to the class
  width like x86, and its division traps.
- **clang folds undefined shifts differently.** clang's folder clamps a
  too-large count to width-1 and turns a negative count into the
  opposite shift (`1 << 32` folds to `INT_MIN`, `8 >> -1` to 16), with
  a warning. That is the `rejected(differs)` class: all shifts.
- **Signed overflow in `+ - * -x` and `<<` wraps in `const_eval`** as in
  clang's and GCC's default folding, which warn; C11 makes it a
  constraint violation in a constant expression (6.6p4), and pedantic
  clang rejects it. nanofil gives no diagnostic. That is the
  `fold_extension` class, and the only place nanofil accepts a constant
  pedantic clang does not. Rejecting it would refuse static initializers
  clang accepts with a warning; that is a decision for later, now
  visible as a class with a count.
- **clang's ICE judgment is not C11's.** Pedantic clang accepts `1 << 31`
  and `3 << 30` (a signed result that is not representable, undefined by
  6.5.7p4) and rejects `-1 << 1`. The overlap is measured against clang,
  so it includes the former; all three readings wrap them alike.

Not compared: `#if` (`Env = pp`, where every type is `intmax_t`), floats,
pointers, `sizeof` and the comma operator; native execution of the IR,
which `difftest.sh` compares separately; and nanofil's `-O` path.

## Running it

```sh
export SWIPL=/tmp/swipl/bin/swipl FILCC=/tmp/filcc/bin/clang
nanofil/tests/arith.sh slice                  # the Nix check's slice, ~11 s
nanofil/tests/arith.sh complete               # every operator over all boundary leaves, ~90 s
nanofil/tests/arith.sh random SEED COUNT DEPTH
```

Each prints the count of every class, a breakdown by root operator,
three examples per class outside the overlap, and every disagreement
with all five readings. The slice is every operator over 18 leaves at
the boundaries that differ (`INT_MIN`, `-1`, `UINT_MAX`, the 64-bit
extremes, counts 31, 32 and 64), plus 400 random trees of depth 3 from
seed 1. Planting each of the three fixes below back makes the slice
fail.

## Results (October 2026)

| Space | Expressions | overlap | fold_extension | rejected: traps / wraps_as_clang / differs | bugs |
|---|---|---|---|---|---|
| complete (depth 1, 53 leaves) | 57,081 | 52,086 | 999 | 1,304 / 1,614 / 1,078 | 0 |
| random 1 5000 4 | 5,000 | 3,373 | 167 | 782 / 548 / 130 | 0 |
| random 2 5000 4 | 5,000 | 3,399 | 170 | 747 / 564 / 120 | 0 |
| random 3 5000 4 | 5,000 | 3,434 | 147 | 751 / 542 / 126 | 0 |
| slice | 7,186 | 6,404 | 211 | 79 / 264 / 228 | 0 |

In the complete space `fold_extension` is only `+`, `-`, `*`, unary `-`
and `<<`; `rejected(differs)` and `rejected(wraps_as_clang)` are only
shifts; `rejected(traps)` only `/` and `%`.

## What it found

Before the fixes, the first random run of 300 expressions had 10
disagreements and the complete space 32 after the shift fix. Each fix
is in `c_types.pl`'s constant folding with a fail-first test.

1. **Shift counts were not checked** (C11 6.5.7p3). `const_eval`
   computed `A << B` on unbounded integers and then wrapped, so `1 << 32`
   folded to 0 (clang: `INT_MIN`, IR: 1), a negative count shifted the
   other way, and `1L << 18446744073709551615u` asked Prolog for a
   number with 2^64 bits: a resource error that crashed the compiler,
   even in code that only asks whether a `?:` arm is a null pointer
   constant. `kind_binary(shift, ...)` now gives `ub` for a count outside
   `[0, width)`. Tests: `tests/c/reject/shift-count.c` (nanofil accepted
   `_Static_assert((1 << 32) == 0)`, which clang's own folding fails),
   `tests/c/constant-ub.c` (`huge_shift`), and `kind_binary/6`'s
   `doc/3` examples.
2. **`MIN / -1` and `MIN % -1` folded** (C11 6.5.5p6) to `MIN` and 0,
   while the IR (and x86 `idiv`) traps. `quotient_overflows/4` makes them
   `ub`, as division by zero already was. Tests:
   `tests/c/reject/division-overflow.c` and `kind_binary/6`'s examples,
   which include the boundary `-INT_MAX / -1` and the same quotient in
   `long`.
3. **A cast of an undefined constant crashed lowering.** Lowering asks
   whether each `?:` arm is a null pointer constant (6.3.2.3p3) by
   folding it to the bound value 0. `const_convert/4`'s first clause,
   `const_convert(ub, _, _, ub)`, does not match when the result is
   bound, so `(long long)(1 / 0)` fell through to `convert_int(ub, ...)`,
   an arithmetic type error. The clause now tests `V0 == ub` before
   unifying. Tests: `tests/c/constant-ub.c` (`cast_quotient`) and
   `const_convert/4`'s new `doc/3`, including
   `fails(const_convert(ub, int, llong, 0))`.

No disagreement was found inside the overlap that the fixes did not
explain: the usual arithmetic conversions, integer promotions, unsigned
wrap, comparisons of mixed signedness, `&&`, `||` and `?:` agreed on
every expression generated.
