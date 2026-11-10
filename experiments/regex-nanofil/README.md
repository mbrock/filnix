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
HOST=tpl ./run.sh            # the same on Trealla, without SWI-Prolog
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
  `ld`. A packaged one would be a saved state, or Trealla at the cost
  under [Trealla](#trealla).
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
| bytecode to IR, Trealla | 0.17 s |
| `nanofil -O compile`, SWI-Prolog with a saved state | 5.1 s |
| `as` | 0.02 s |
| `clang -shared` | 0.06 s |

`nanofil -O compile` of one function alone takes 0.15 s (`lit`, 550 lines of
assembly) to 0.6 s (`nested`, 3000 lines). That is the LLVM JIT's range (44
to 300 ms) and far from sljit's 0.1 ms, which is why the hook caches on
disk. When the module had nine functions (1.7 s), nanofil's profile put the
time in the register-allocation checker (`amd64_regs_check`), assoc
operations and garbage collection.

## The compiler extracted from Rocq

`NANOFIL_BACKEND=.../nanofil-backend` makes `rxc` and `run.sh` compile the
IR with `nanofil-backend compile`, the backend extracted from Rocq
(`nanofil/rocq/backend`, `nanofil/docs/gallina-backend.md`), so that no
Prolog runs after `rx.pl`. It is the compiler without `-O`, and its
assembly for the module of 36 is `nanofil compile`'s byte for byte. `bench`
and `hook` pass with it. Measured on November 10:

- The module compiles in 0.39 s, against 1.4 s for `nanofil compile` and
  6.3 s for `nanofil -O compile`.
- A cold cache of the hook's 39 patterns takes 4.6 s, against 12.8 s: 120
  ms a miss against 330. Of one miss, `rx.pl` is 44 to 58 ms, the backend
  16 to 43 ms, `as` 7 to 12 ms and `ld` 17 to 19 ms.
- The code is slower: 2.7 to 16 times `-O`'s per call on the nine patterns
  above (6.2 times in the geometric mean), which is still 1.5 to 3.5 times
  faster than the interpreter.
- What the code needs from `-O` is promotion with copy propagation (2.3
  times), registers (1.7 to 2 times) and selected branches (1.1 to 1.6
  times). `--simplify=none`, `--inline=none`, `--checks=reference` and
  `--memcpy=call` each change the time by under a tenth. The whole list is
  in `nanofil/docs/gallina-backend.md`.

## Trealla

`rx.pl` runs on the Trealla that `nanofil/nix/trealla.nix` pins, and since
`c95fa9f0` so does nanofil's back end. `NANOFIL_HOST=trealla` makes `rxc`
run both Prolog steps there, and `HOST=tpl ./run.sh` runs the whole recipe
without SWI-Prolog. nixpkgs' Trealla 2.99.1 prints nothing for `rx.pl`.

The output is SWI-Prolog's, byte for byte:

- IR and assembly of the 39 patterns `hook.c` compiles, each alone, and
  the assembly of the module of 36;
- the 39 shared objects of a cache that `rxc` filled on Trealla, with which
  `hook.c` passes as above;
- the shared objects of 346 patterns of PCRE2's tests, every fourth of the
  1383 that rx compiles;
- the assembly of the 39 from the Trealla that Fil-C compiles
  (`pkgsFilc.trealla`, the same revision), with the default registers and
  with `--registers=stack`.

What differs is the cost. `nanofil -O compile` of one pattern, over the 39:

| Host | Load | Compile, median | Compile, longest | Peak memory |
| --- | ---: | ---: | ---: | ---: |
| SWI-Prolog, saved state | 0.05 s | 0.2 s | 0.7 s | 43 MB |
| Trealla | 0.5 s | 0.40 s | 2.8 s | 0.63 GB |
| Trealla, `--registers=stack` | 0.5 s | 0.15 s | 0.7 s | 0.23 GB |
| Fil-C Trealla | 2.8 s | 2.4 s | 17 s | 2.1 GB |
| Fil-C Trealla, `--registers=stack` | 2.6 s | 0.87 s | 4.2 s | 0.80 GB |

- The Trealla rows are one process that loads nanofil once and compiles the
  39 in turn, as a compiler embedded in a long-lived process would. It is a
  scratch copy of `main.pl` with a loop in place of `main` and without the C
  front end and the interpreter; with them loading takes 0.9 s (4.8 s
  on Fil-C Trealla). The peak memory is the largest pattern's, which
  needs 0.6 GB alone.
- These are for the pin of November 10 (`98a821db` and
  `patches/trealla-heap-page-mark.patch`). The pin of September 5 took
  1.5 times as long and three times the memory: 0.58 s median, 4.0 s
  longest and 1.9 GB native, 4.0 s, 26 s and 7.5 GB under Fil-C.
  `nanofil/docs/archive/hosts.md` says where the time and memory go.
- `rxc` starts a process per pattern and loads all of `main.pl`, so it takes
  1.0 to 4.1 s per pattern on Trealla (median 1.4 s; 11 s for the slowest of
  the 346) against 0.15 to 0.8 s on SWI-Prolog. Filling the cache for the
  39 takes 62 s instead of 13 s.
- The whole module of 36 functions takes 23 s and 1.6 GB on Trealla, 5.5 s
  and 48 MB on SWI-Prolog.
- `--registers=stack` skips the register allocator and its checker. Its
  code is 1.1 to 1.7 times slower in the direct-call loop above (`tag` 91 to
  148 ns, `email` 2033 to 3513, `word` 26 to 37), which is still far ahead
  of the interpreter. Measured again on November 10 it is 1.6 to 2.9
  times slower (`tag` 109 to 290 ns, `email` 2249 to 6322, `word` 26 to
  78).

So the regex compiler no longer needs SWI-Prolog, and what an embedded
Trealla would cost is known:

- libpcre2 is Fil-C code, so a Trealla inside it is Fil-C Trealla, five to
  six times slower than the native one: the first miss in a process pays 2.7 s
  of loading, and each miss 0.9 to 17 s and up to 2.1 GB in that process.
  A native `tpl` as a child process costs 1 to 4 s per miss.
- nanofil's entry point is its command line: `main.pl` holds the defaults
  of `-O` and halts when done. Calling it from a host needs that split in
  nanofil; the scratch copy stands in for it here.
- Trealla has no saved state, so nanofil's sources are read on every start.
- `as` and `ld` are still separate programs.
