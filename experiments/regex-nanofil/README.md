# A regex compiler that targets nanofil's IR

An exploration for [docs/pcre2-jit.md](../../docs/pcre2-jit.md): instead of
running PCRE2's JIT, compile the regex to Fil-C code with nanofil.

`dump.c` prints the bytecode that `pcre2_compile` made of each pattern, and
`rx.pl` (728 lines of Prolog) decodes it and emits one function of nanofil's
unchecked IR per pattern. nanofil then treats it like lowered C: it inserts
the Fil-C checks, optimizes, and prints assembly. `as` and a linker make a
shared object that a Fil-C program loads with `dlopen`. The regex compiler
needs no change to nanofil and is outside the safety argument: a wrong
offset in the generated code is a Fil-C panic.

A patch to libpcre2 ([the hook](#the-hook)) does this behind PCRE2's own JIT
API: `pcre2_jit_compile` finds or builds the pattern's shared object in a
cache directory, and `pcre2_match` calls it.

```sh
../pcre2-sljit-llvm/run.sh   # once: builds the toolchain and Fil-C PCRE2
./run.sh                     # compile the patterns, check and time them,
                             # then build the hooked libpcre2 and check it
HOST=tpl ./run.sh            # the same, with bytecode to IR on Trealla
```

## Why the bytecode

`rx.pl` first parsed regex text. It now reads what PCRE2's interpreter and
sljit read, so PCRE2 keeps the parts that define its dialect:

- the syntax, group numbering, inline options and named groups;
- case folding, which arrives as class bitmaps and caseless opcodes;
- counted groups, which arrive as copies: `rx.pl` only sees groups repeated
  zero or one time or without limit;
- auto-possessification, and the start information (anchored, first code
  unit, start bitmap) that the start scan uses.

`dump.c` also prints the opcode numbering of the PCRE2 it is built against,
in `rx.pl`'s terms, so `rx.pl` holds no opcode numbers. An opcode it does
not name reaches `rx.pl` as `x('NAME')` and makes the pattern unsupported.

`dump.c` and the hook share the code that prints the terms
(`pcre2_rx_terms.h`), which reads `pcre2_real_code`. Operand layouts (two-byte
links and counts, 32-byte class bitmaps) are still written into `rx.pl`.

## The function

```c
int rx_NAME(const char *subject, long length, long start,
            long *ovector, long *stack, long slimit, long budget);
```

It returns 1 with the ovector filled as PCRE2 fills it, 0 for no match, -1
when the backtrack stack of `slimit` longs is too small, and -2 when it has
backtracked into a loop or an alternation more than `budget` times, which
is how the hook keeps PCRE2's match limit. Choice state lives in
`alloc` slots that nanofil promotes to SSA; only a loop over a group uses the
stack. The start scan skips bytes that cannot begin a match, with `memchr`
when only one byte can. The header of `rx.pl` describes the code shape.

## What it compiles

8-bit patterns without UTF or UCP, with the LF newline and the built-in
character tables: characters and classes with their greedy, lazy and
possessive repeats, `.`, `^ $ \A \z \Z \b \B` with or without multiline,
dotall and `DOLLAR_ENDONLY`, alternation, capturing, plain and atomic groups
and their greedy, lazy and possessive repeats, lookahead, and fixed-length
lookbehind.

A pattern with anything else is reported as unsupported and stays on the
interpreter: UTF and Unicode properties, backreferences, recursion and
subroutine calls, conditions, verbs, callouts, variable-length lookbehind,
`\G`, `\K`, `\R`, `\X`, `\C`, other newline conventions, custom character
tables, a leading `(*NOTEMPTY)`, and the compile options `FIRSTLINE`,
`ENDANCHORED` and `ALT_CIRCUMFLEX`.

The function takes no match options, so `NOTBOL`, `NOTEOL`, `NOTEMPTY`,
`ANCHORED` at match time, partial matching, an offset limit and the depth
limit are not handled either. The hook sends those calls to the interpreter.

## The check

`bench.c` calls both matchers from every start offset of the subject and
requires the same result and the same whole ovector. It does that for the
ten patterns of `pats.h` and for 28 more in `more.h` that exist to exercise
the decoder: atomic and possessive groups, lookbehind, multiline, counted
and lazy group loops, loops whose body can match nothing, and captures that
backtracking or a failed lookaround must undo, named groups and inline
options.

- 36 of the 38 compile, and all 36 agree: 6129 calls each on the HTML
  subject, 65 on the short one.
- `utf` and `backref` are reported as unsupported.
- Ten deliberate bugs in `rx.pl` (an empty iteration that loops again, an
  atomic group that can be resumed, captures not undone, an optional group
  tried in the wrong order, and the like) were each caught by at least one
  pattern. The mutants are not kept in the tree.

`hook.c` and PCRE2's own tests check the same functions through
`pcre2_match`; see below.

## The hook

`pcre2-rx-hook.patch` applies to PCRE2 10.49 (`pkgsFilc.pcre2` is 10.48
today) after `patches/pcre2-10.48-filc-match.patch`, and `pcre2_rx_inc.h` and
`pcre2_rx_terms.h` go into its `src/`. In an 8-bit library built for Fil-C
with `--disable-jit`, the JIT API is then served by rx. A caller that
already uses `pcre2_jit_compile` needs no change.

`pcre2_jit_compile(code, PCRE2_JIT_COMPLETE)` prints the bytecode as terms,
hashes the text into a key, and looks in the cache directory:

| File | Content |
| --- | --- |
| `KEY.pl` | the terms, compared byte for byte, so a hash collision is a miss |
| `KEY.so` | the shared object, exporting `rx_m` |
| `KEY.no` | instead of `KEY.so`: the pattern is unsupported, and why |
| `KEY.log` | what the compiler printed |

On a miss it runs `COMPILER KEY.pl OUTPUT` with `posix_spawn` and waits.
Exit status 0 caches the shared object, 1 caches the `.no`, and anything
else caches nothing. `rxc` is that compiler: `rx.pl`, `nanofil -O compile`,
`as` and `ld -shared`, with a 10 s limit (`RXC_SECONDS`) on the Prolog
steps, past which the pattern counts as unsupported.

Two environment variables switch it on. Both are read with `secure_getenv`,
so a set-id program ignores them.

- `PCRE2_RX_CACHE` is the cache directory: an absolute path that belongs to
  the effective user or to root and that nobody else can write, because
  what is in it is loaded as code. `dlopen` does not check that a shared
  object came from nanofil, so whoever can write the directory is trusted
  like whoever can write a library the program links.
- `PCRE2_RX_COMPILER` is the compiler. Without it the cache is only read.

Without a usable cache directory the library behaves as one built with
`--disable-jit`: `pcre2_jit_compile` returns `PCRE2_ERROR_JIT_BADOPTION` and
`PCRE2_CONFIG_JIT` is 0.

`pcre2_match` calls the function when the code has one and returns to the
interpreter, which then runs the whole match, in three cases:

- a match option other than `NO_UTF_CHECK` and `COPY_MATCHED_SUBJECT`, or
  an offset limit;
- a backtrack stack that would pass the heap limit. The stack lives in the
  match data, starts at 1024 longs and doubles;
- the match limit, so that the interpreter decides what a limit means.

The key covers the bytecode and the hook's interface number, not the
version of `rx.pl` or nanofil, so a cache directory belongs to one compiler.

### Checks

`hook.c` uses the public API only. It compiles each pattern twice, gives
one copy to `pcre2_jit_compile`, and from every start offset compares
return value, ovector, start character and substring length: with four
ovector sizes, through `pcre2_jit_match`, with `COPY_MATCHED_SUBJECT`, with
seven options that fall back, with a heap limit of 1, with an offset limit,
and through `pcre2_substitute`. Besides the 38 patterns above it has three
that need a deep backtrack stack or hit a match limit.

- 39 of the 41 compile and all agree; `utf` and `backref` stay on the
  interpreter.
- Nine deliberate bugs in the hook (the option fallback, the return count,
  the small-ovector copy, stack growth, the offset and heap limits, the
  start character and others) were each caught. A tenth was not: leaving
  the pattern's own `(*LIMIT_MATCH)` out of the budget, which the
  interpreter fallback hides.
- No cache, a relative path and a group-writable directory all leave the
  JIT off. A compiler that fails or is missing caches nothing. A corrupt
  `KEY.so` leaves the pattern on the interpreter.

PCRE2's tests, run as `pcre2test -q -jit` against an empty cache:

- `testinput1` gives exactly `testoutput1`.
- `testinput2`, without its `#loadtables` line, gives exactly the output of
  the same build with the JIT off.
- Of their 2485 distinct patterns, 1383 were compiled and 1102 were not.
  The commonest reasons: conditions 178, recursion 147, backreferences 124,
  `(*MARK)` 85, `(*THEN)` 66, callouts 61. Eight ran into the 10 s limit;
  one of them, 146 KB of bytecode, takes 77 s.
- A function that always answers "no match" changes 1281 of the 1976
  matches in `testinput1`, so the suite does run the compiled code.

`pcre2test -C` still says there is no JIT, and `-jit` prints a warning:
that is `pcre2test`'s own compile-time test.

### Cost

Nanoseconds per call in the find-all loop, both columns through
`pcre2_match` of the hooked library. The interpreter here has the match
patch, so it is faster than the "Fil-C interpreter" column below.

| Pattern | Interpreter | Hook | Speedup | `pcre2_jit_match` |
| --- | ---: | ---: | ---: | ---: |
| tag | 1028 | 118 | 8.7× | 107 |
| email | 34633 | 2005 | 17× | 2024 |
| word | 188 | 50 | 3.8× | 35 |
| alt | 3505 | 746 | 4.7× | 721 |
| entity | 341 | 76 | 4.5× | 64 |
| shortcode | 1484 | 224 | 6.6× | 176 |
| key | 192 | 59 | 3.2× | 46 |
| date | 583 | 50 | 12× | 36 |
| lit | 1982 | 295 | 6.7× | 274 |

- `pcre2_match` adds about 25 to 35 ns to the direct call measured below
  (`word`: 23 ns direct, 50 through the hook), and `pcre2_jit_match` skips
  10 to 20 ns of that.
- `pcre2_jit_compile` on a miss takes 0.15 to 0.8 s: 12 s for the 39
  patterns, median 0.2 s and 99th percentile 1.0 s over PCRE2's tests. The
  caller waits for it.
- On a hit it takes 0.3 to 0.9 ms the first time, and about 0.12 ms when
  the same pattern is compiled, loaded and freed in a loop. Without a
  cache directory the call costs 8 µs.
- A pattern known to be unsupported costs about 0.12 ms per
  `pcre2_jit_compile`.

### Open

- Where the cache lives and who fills it: per user on first use, as here,
  or a system directory filled when a package is built.
- The compiler is a checkout of this repository plus SWI-Prolog, `as` and
  `ld`. A packaged one would be a saved state, or `rx.pl` on Trealla once
  nanofil's back end runs there.
- The key should cover the compiler's version once one is shipped.
- Conditions, recursion, backreferences and the backtracking verbs are the
  unsupported opcodes that PCRE2's tests use most.
- UTF and UCP patterns are not compiled at all.

## Measurements

Nanoseconds per call in the find-all loop, same subject and orb as
`docs/pcre2-jit.md`, whose numbers the first and last columns repeat. Runs
vary by about 10%.

| Pattern | Native sljit | Fil-C interpreter | rx | Speedup | Fil-C LLVM JIT |
| --- | ---: | ---: | ---: | ---: | ---: |
| tag | 75 | 1338 | 93 | 14× | 347 |
| email | 702 | 30607 | 1943 | 16× | 1706 |
| word | 24 | 424 | 23 | 18× | 93 |
| alt | 259 | 4226 | 874 | 4.8× | 535 |
| entity | 82 | 579 | 47 | 12× | 286 |
| shortcode | 588 | 1033 | 156 | 6.6× | 861 |
| key | 25 | 385 | 30 | 13× | 97 |
| date | 24 | 524 | 21 | 25× | 171 |
| lit | 258 | 2344 | 263 | 8.9× | 342 |

- These are the text parser's speeds within the run-to-run variation. `alt`
  varied most: 690, 800 and 870 ns in three builds with the same IR for it.
- rx is called directly, while the interpreter and native sljit columns go
  through `pcre2_match`. The table under [Cost](#cost) has rx through
  `pcre2_match`.
- Before the `memchr` start scan, `lit`, `entity` and `shortcode` took 1147,
  345 and 1127 ns: the scan loop pays a bounds check and a pollcheck per byte.
- `email` and `alt` are behind sljit and the LLVM JIT. `email` restarts
  `[\w.]+@` at every word byte, and `alt` tests its arms one after another.
- nanofil without `-O` makes code 5 to 10 times slower. The `--checks`
  variants barely differ.

Compile time, all 36 functions in one module (27000 lines of assembly):

| Step | Time |
| --- | ---: |
| bytecode to IR, SWI-Prolog | 0.07 s |
| bytecode to IR, Trealla | 0.16 s |
| `nanofil -O compile`, SWI-Prolog with a saved state | 5.1 s |
| `as` | 0.02 s |
| `clang -shared` | 0.06 s |

`nanofil -O compile` of one function alone takes 0.15 s (`lit`, 550 lines of
assembly) to 0.6 s (`nested`, 3000 lines). That is the LLVM JIT's range (44
to 300 ms) and far from sljit's 0.1 ms, which is why the hook caches on
disk. When the module had nine functions (1.7 s), nanofil's profile put the
time in the register-allocation checker (`amd64_regs_check`), assoc
operations and garbage collection.

## Trealla

- `rx.pl` runs unchanged on the Trealla that `nanofil/nix/trealla.nix` pins
  and prints the same IR as on SWI-Prolog for all 36 patterns. nixpkgs' Trealla 2.99.1 prints
  nothing.
- `NANOFIL_HOST=trealla bin/nanofil` no longer works. It loads in 1.5 s with
  a DCG error at `c_parse.pl:859`; then `-O compile` of an IR file ends in an
  instantiation error, and plain `compile` in a missing `partition/4`.
- Without the C frontend (`ir_text`, `opt`, `pizlonate`, `filc_amd64` and
  what they import), nanofil loads on Trealla in 1.0 s, against 0.45 s from
  source and 0.06 s from a saved state on SWI-Prolog. It needs `partition/4`
  and `select/4`, which Trealla's libraries lack.
- Reading, optimizing and pizlonating the earlier nine-function module takes
  1.9 s on Trealla and 0.25 s on SWI-Prolog. `filc_module_emit` fails on
  Trealla with `syntax_error(operator_expected)` from `number_codes/2`; I did
  not trace it.

So Trealla can host the regex compiler today, and hosting nanofil's back end
on it is a port: a few library predicates, one bug, and a factor of about
seven in speed.
