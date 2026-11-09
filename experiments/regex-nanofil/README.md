# A regex compiler that targets nanofil's IR

An exploration for [docs/pcre2-jit.md](../../docs/pcre2-jit.md): instead of
running PCRE2's JIT, compile the regex to Fil-C code with nanofil.

`dump.c` prints the bytecode that `pcre2_compile` made of each pattern, and
`rx.pl` (715 lines of Prolog) decodes it and emits one function of nanofil's
unchecked IR per pattern. nanofil then treats it like lowered C: it inserts
the Fil-C checks, optimizes, and prints assembly. `as` and `clang -shared`
make a shared object that a Fil-C program loads with `dlopen`. The regex
compiler needs no change to nanofil and is outside the safety argument: a
wrong offset in the generated code is a Fil-C panic.

```sh
../pcre2-sljit-llvm/run.sh   # once: builds the toolchain and Fil-C PCRE2
./run.sh                     # compile the patterns, check and time them
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

`dump.c` stands in for a hook inside libpcre2: it includes
`pcre2_internal.h` to read `pcre2_real_code`. Operand layouts (two-byte
links and counts, 32-byte class bitmaps) are still written into `rx.pl`.

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

## What it compiles

8-bit patterns without UTF or UCP, with the LF newline and the built-in
character tables: characters and classes with their greedy, lazy and
possessive repeats, `.`, `^ $ \A \z \Z \b \B` with or without multiline,
dotall and `DOLLAR_ENDONLY`, alternation, capturing, plain and atomic groups
and their greedy, lazy and possessive repeats, lookahead, and fixed-length
lookbehind.

A pattern with anything else is reported as unsupported and would stay on
the interpreter: UTF and Unicode properties, backreferences, recursion and
subroutine calls, conditions, verbs, callouts, variable-length lookbehind,
`\G`, `\K`, `\R`, `\X`, `\C`, other newline conventions, custom character
tables, a leading `(*NOTEMPTY)`, and the compile options `FIRSTLINE`,
`ENDANCHORED` and `ALT_CIRCUMFLEX`.

The function takes no match options, so `NOTBOL`, `NOTEOL`, `NOTEMPTY`,
`ANCHORED` at match time, partial matching and the match and depth limits
are not handled either. A hook would send those calls to the interpreter.

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

This is far from PCRE2's own test suite, which is the check a real version
needs.

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
  through `pcre2_match`. A hook inside `pcre2_match` would add its argument
  checks and match-data setup to the rx column.
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
| `nanofil -O compile`, SWI-Prolog with a saved state | 4.7 s |
| `as` | 0.02 s |
| `clang -shared` | 0.06 s |

`nanofil -O compile` of one function alone takes 0.15 s (`lit`, 550 lines of
assembly) to 0.6 s (`nested`, 3000 lines). That is the LLVM JIT's range (44
to 300 ms) and far from sljit's 0.1 ms, so compiled patterns must be cached
on disk or built ahead of time. When the module had nine functions (1.7 s),
nanofil's profile put the time in the register-allocation checker
(`amd64_regs_check`), assoc operations and garbage collection.

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
