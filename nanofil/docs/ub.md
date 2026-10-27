# Undefined behaviour under Fil-C, and nanofil's choices

Fil-C does not give C's undefined behaviour a meaning in general. It
guarantees memory safety whatever the program does (GIMSO,
`gimso_semantics.md` in the reference source), and it takes away the
licence LLVM's optimizer would otherwise read into UB. This page states
what that amounts to for each common kind of UB, with the source that
causes it and what [`probes/ub.c`](../probes/ub.c) observed, then where
nanofil agrees and differs. Fil-C's own documentation covers pointers
and capabilities but says nothing about integer UB; everything here
comes from the pass source and probes.

Observed at staging `af813053ecb5` (`lib/filc-staging.json`), reading
`nix build .#lib.x86_64-linux.filc-staging-ref-src`, x86-64, October 2026.

## Where UB is removed: KillUB, before any optimization

`clang/lib/CodeGen/BackendUtil.cpp` registers one pipeline-start
callback, so this order holds at every `-O` level:

```diagram
clang Sema + CodeGen (unchanged clang 20: constant folding, ICE rules)
        │
        ▼
KillUB ──▶ (O1+) SROA, EarlyCSE, inliner with InstCombine/GVN/SCCP/CVP…
        │
        ▼
CoroSplit ──▶ FilPizlonator (checks, flight pointers, frames)
        │
        ▼
the ordinary LLVM -O pipeline ──▶ DeleteRedundantPollchecks
```

`llvm/lib/Transforms/Instrumentation/KillUB.cpp` (107 lines; its own
comment: "This is just the beginning! There are probably more UB
killings that have to happen.") does four things to every function:

| What | Effect |
| --- | --- |
| `dropPoisonGeneratingAnnotations` | removes `nsw`, `nuw`, `exact`, `inbounds`, `disjoint` and similar: signed overflow and out-of-range `gep` become ordinary wrapping arithmetic |
| `dropUnknownNonDebugMetadata` | removes all non-debug metadata, including `!tbaa`, `!range`, `!nonnull`, `!noalias` |
| attribute mask | removes `noundef`, `nonnull`, `dereferenceable`, `noalias`, `readonly`/`writeonly`/`memory`, `noreturn`, `willreturn`, `mustprogress`, `nofree`, `nosync`, `range`, `returned` and others from functions, returns and parameters |
| intrinsics | erases `llvm.assume`, `noalias.scope.decl` and `invariant.start`/`.end`; replaces `launder`/`strip.invariant.group` by their operand |

It does **not** change instruction semantics that are UB in LLVM by
themselves: `sdiv`/`udiv` by zero, `sdiv MIN, -1`, `shl`/`lshr`/`ashr`
by at least the width (poison), `fptosi` out of range (poison),
`unreachable`, `undef` from an uninitialized scalar. A reached
`unreachable` that survives to pizlonation becomes a Fil-C panic,
"llvm unreachable instruction" (`FilPizlonator.cpp`, the
`UnreachableInst` case), as does `llvm.trap`. Optimizations that run
before pizlonation at `-O1` and up may still exploit these.

After pizlonation LLVM may again infer `nsw`/`nuw` from facts it
proves itself (the probe's loop counter gets `add nuw nsw`). Those are
derived, not read from the source's UB.

Memory safety does not depend on any of this: the pizlonator checks
whatever IR it receives. The probe `unreach-idx` shows the
distinction. At `-O2`, `if (i >= 4) __builtin_unreachable(); return g[i];`
with `i = 10` loses its `unreachable` panic, because the optimizer
exploited it, but the bounds check still panics.

## What each kind of UB does

`-O0` and `-O2` are filcc; `progtest.sh` and the corpus compare against
filcc `-O1`, which behaved as `-O2` on every probe below.

| C11 | Probe | Fil-C `-O0` | Fil-C `-O2` | Why | nanofil |
| --- | --- | --- | --- | --- | --- |
| signed `+ - *` overflow (6.5p5) | `inc`: `x + 1 > x`, `x = INT_MAX` | 0 | 0 | `nsw` dropped; it wraps, and `-O2` compiles it to `x != INT_MAX` | wraps: 0 |
| `-INT_MIN` | `neg` | `INT_MIN` | `INT_MIN` | wraps | wraps |
| shift count ≥ width (6.5.7p3) | `shl`: `1 << 32` | 1 | 1 | LLVM poison; x86 `shl` masks the count | IR masks the count: 1 |
| check after an oversized shift | `shl-check` | -1 | -1 | the later `n >= 32` test was kept | -1 |
| `x / 0`, `INT_MIN / -1` (6.5.5p5-6) | `div0`, `min-1`, `div-check` | SIGFPE (136) | SIGFPE (136) | `idiv` faults; not a Fil-C panic. `-O2` did not hoist the `d == 0` test above the division | interpreter `ub(division_by_zero)` / `ub(division_overflow)`; native SIGFPE |
| strict aliasing (6.5p7) | `tbaa`: `*i = 1; *f = 2.0f; return *i;` | 0x40000000 | 0x40000000 | `!tbaa` dropped; memory is bytes | bytes: same |
| uninitialized automatic (6.7.9p10, 6.3.2.1p2) | `uninit`: `int x; if (c) x = 5; return x;`, `c = 0` | 0 | **5** | allocations are zeroed, but SROA makes `x` an SSA `undef` before pizlonation, and the select folds | 0: interpreter zeroes allocations; `promote` starts slots at `initial_zero` |
| out-of-range float to int (6.3.1.4p1) | `fp`: `(int)1e20` | `INT_MIN` | `INT_MIN` | `cvttsd2si`'s indefinite value; LLVM poison | interpreter `ub(float_conversion)`; native `INT_MIN` |
| `__builtin_unreachable` reached | `unreach` | panic | **returns 7** | `unreachable` exploited before pizlonation | `unreachable`: interpreter outcome; native `ud2`, SIGILL (132) |
| out of bounds after wrap | `wrap-idx`: `j = i + 1` with `i = INT_MAX`, then `g[j]` | panic `ptr < lower` | panic | the wrapped index is checked | panic |
| null dereference, then a null test | `null` | panic | panic | `nonnull` dropped; the check is on the access | panic |

C11 references are to the paragraph making the behaviour undefined.
Memory-safety violations (bounds, null, use after free, rights) are
always panics; that is the GIMSO guarantee, not an optimization choice.

## Constant expressions are clang's

Fil-C leaves clang's Sema unchanged. An integer constant expression is
judged and folded exactly as by upstream clang 20: `_Static_assert`,
`case` labels and array sizes reject a signed overflow or an oversized
shift (6.6p4), while a static initializer folds it with a warning (the
default, non-pedantic mode). Signed overflow then wraps, and an
oversized shift count is clamped to width − 1 (`1 << 32` folds to
`INT_MIN`), which differs from the masked runtime result above.

[arith.md](arith.md) measures nanofil's `const_eval` against this.
nanofil refuses an oversized shift or an undefined quotient in every
constant context, and wraps signed overflow without a diagnostic (its
`fold_extension` class). The wrap agrees with what Fil-C computes,
both when folding a static initializer and at run time. Only
pedantic clang rejects it.

## nanofil's position

nanofil's IR has no poison, `undef` or UB flags. Integer operations
wrap at their class width, shift counts are masked as on x86, and
division by zero or `MIN / -1` is the one integer operation the
interpreter treats as undefined; native code faults, as Fil-C's does.
Memory is bytes, with no type-based aliasing. Allocations start zeroed.
This is Fil-C's behaviour at `-O0`, and it is what KillUB makes of the
source's UB. Where Fil-C's later optimizations still exploit LLVM's own
UB (uninitialized scalars, `unreachable`), nanofil stays deterministic.

So programs that read an uninitialized scalar or reach
`__builtin_unreachable` can differ from the `-O1` reference in
`progtest.sh` and the corpus. That is a difference in the reference,
not a nanofil bug. Such a test is not a valid comparison.

Differences worth closing or keeping in mind:

- **A reached `unreachable` is SIGILL in nanofil, a Fil-C panic in
  clang `-O0`.** `filc_amd64.pl`'s `jump(unreachable, ...)` emits `ud2`;
  Fil-C calls its error routine with an origin. `progtest.sh` normalizes
  only `filc safety error` output to `trap`, so these do not compare
  equal.
- **Constant contexts:** `const_eval` wraps signed overflow where C11
  6.6p4 requires a diagnostic. This matches clang's default folding of
  static initializers; making it `ub` would refuse initializers clang
  accepts with a warning.
- Not probed: infinite loops without side effects (KillUB removes
  `mustprogress`, so C11 6.8.5p6 is not exploited), signed overflow in
  `++` on a pointer-sized index, `ctlz`/`cttz` of zero from
  `__builtin_clz(0)`, and atomics.

## Reproduce

```sh
nix build -o /tmp/filcc .#filcc-staging
for O in O0 O2; do /tmp/filcc/bin/clang -$O -w nanofil/probes/ub.c -o /tmp/ub-$O; done
for t in inc neg shl shl-check div0 div-check min-1 tbaa uninit fp \
         unreach unreach-idx wrap-idx null; do
  for O in O0 O2; do /tmp/ub-$O $t; echo "$t $O exit $?"; done
done
# nanofil: (cd nanofil/src && ../bin/nanofil cc ../probes/ub.c </dev/null) >ub.s,
# then as and link with filcc as progtest.sh does.
```
