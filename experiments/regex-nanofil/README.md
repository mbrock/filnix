# A regex compiler that targets nanofil's IR

An exploration for [docs/pcre2-jit.md](../../docs/pcre2-jit.md): instead of
running PCRE2's JIT, compile the regex to Fil-C code with nanofil.

`rx.pl` (690 lines of Prolog) parses a PCRE subset and emits one function of
nanofil's unchecked IR per pattern. nanofil then treats it like lowered C: it
inserts the Fil-C checks, optimizes, and prints assembly. `as` and
`clang -shared` make a shared object that a Fil-C program loads with `dlopen`.
The regex compiler needs no change to nanofil and is outside the safety
argument: a wrong offset in the generated code is a Fil-C panic.

```sh
../pcre2-sljit-llvm/run.sh   # once: builds the toolchain and Fil-C PCRE2
./run.sh                     # compile the patterns, check and time them
HOST=tpl ./run.sh            # the same, with regex to IR on Trealla
```

`bench.c` runs the find-all loop of `../pcre2-sljit-llvm/bench.c` with both
matchers and requires every call to return the same result and ovector as
PCRE2's interpreter before it times them.

## The function

```c
int rx_NAME(const char *subject, long length, long start,
            long *ovector, long *stack, long slimit);
```

It returns 1 with the ovector filled as PCRE2 fills it, 0 for no match, and -1
when the backtrack stack of `slimit` longs is too small. Choice state lives in
`alloc` slots that nanofil promotes to SSA; only a loop over a group uses the
stack. The start scan skips bytes that cannot begin a match, with `memchr`
when only one byte can. The header of `rx.pl` describes the code shape.

## The subset

Bytes only. Literals, `.`, classes, `\d \w \s` and their negations,
`^ $ \b \B`, alternation, capturing and `(?:)` groups, `(?=)` and `(?!)`,
greedy and lazy quantifiers, possessive ones on a single character, and the
caseless option. Nine of the ten patterns in `pats.h` fit; `utf`
(`\p{Lu}\p{Ll}+`) does not.

Not covered: UTF and Unicode properties, backreferences, recursion and
subroutine calls, atomic groups, lookbehind, named groups, inline options,
multiline and dotall, callouts, partial matching, match limits, and the
newline conventions other than LF.

## Measurements

Nanoseconds per call, same subject and orb as `docs/pcre2-jit.md`, whose
numbers the first and last columns repeat. Runs vary by about 10%.

| Pattern | Native sljit | Fil-C interpreter | rx | Speedup | Fil-C LLVM JIT |
| --- | ---: | ---: | ---: | ---: | ---: |
| tag | 75 | 1244 | 94 | 13× | 347 |
| email | 702 | 33368 | 2293 | 15× | 1706 |
| word | 24 | 421 | 22 | 19× | 93 |
| alt | 259 | 4035 | 860 | 4.7× | 535 |
| entity | 82 | 626 | 50 | 13× | 286 |
| shortcode | 588 | 1065 | 148 | 7.2× | 861 |
| key | 25 | 437 | 31 | 14× | 97 |
| date | 24 | 554 | 22 | 26× | 171 |
| lit | 258 | 2368 | 260 | 9.1× | 342 |

- rx is called directly, while the interpreter and native sljit columns go
  through `pcre2_match`. A hook inside `pcre2_match` would add its argument
  checks and match-data setup to the rx column.
- Before the `memchr` start scan, `lit`, `entity` and `shortcode` took 1147,
  345 and 1127 ns: the scan loop pays a bounds check and a pollcheck per byte.
- `email` and `alt` are behind sljit and the LLVM JIT. `email` restarts
  `[\w.]+@` at every word byte, and `alt` tests its arms one after another.
- nanofil without `-O` makes code 5 to 10 times slower. The `--checks`
  variants barely differ.

Compile time, all nine functions in one module (8200 lines of assembly):

| Step | Time |
| --- | ---: |
| regex to IR, SWI-Prolog | 0.09 s |
| regex to IR, Trealla | 0.10 s |
| `nanofil -O compile`, SWI-Prolog with a saved state | 1.7 s |
| `as` | 0.01 s |
| `clang -shared` | 0.08 s |

One pattern alone takes 0.2 to 0.6 s end to end, of which 0.18 s is the
fixed cost of starting the four processes. That is the LLVM JIT's range (44 to 300 ms) and far from sljit's
0.1 ms, so compiled patterns must be cached on disk or built ahead of time.
In nanofil's profile the time is in the register-allocation checker
(`amd64_regs_check`), assoc operations and garbage collection.

## Trealla

- `rx.pl` runs unchanged on the Trealla that `nanofil/nix/trealla.nix` pins
  and prints the same IR as on SWI-Prolog. nixpkgs' Trealla 2.99.1 prints
  nothing.
- `NANOFIL_HOST=trealla bin/nanofil` no longer works. It loads in 1.5 s with
  a DCG error at `c_parse.pl:859`; then `-O compile` of an IR file ends in an
  instantiation error, and plain `compile` in a missing `partition/4`.
- Without the C frontend (`ir_text`, `opt`, `pizlonate`, `filc_amd64` and
  what they import), nanofil loads on Trealla in 1.0 s, against 0.45 s from
  source and 0.06 s from a saved state on SWI-Prolog. It needs `partition/4`
  and `select/4`, which Trealla's libraries lack.
- Reading, optimizing and pizlonating the nine-function module then takes
  1.9 s on Trealla and 0.25 s on SWI-Prolog. `filc_module_emit` fails on
  Trealla with `syntax_error(operator_expected)` from `number_codes/2`; I did
  not trace it.

So Trealla can host the regex compiler today, and hosting nanofil's back end
on it is a port: a few library predicates, one bug, and a factor of about
seven in speed.
