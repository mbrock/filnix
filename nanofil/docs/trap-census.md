# Campaign 7 step 0: trap-obligation census

Measured on 7 November 2026, against base revision
`1fc35aa711f9b5f01983b91bd4f7afa69e0b6c00` and this page's census tools.
The first measurement used `3e5063a`; the intervening dominance proofs
change no compiler or validator definitions, and the census is rerun.
This is an inventory, **not a trap-freedom proof**. No libc contract has
been discharged or newly probed here. The entry contract remains any
well-formed argv and environment; no restriction to the test inputs,
locale, string lengths or successful allocations is assumed.

## Unit and reproduction

The unit is `nanofil-hello-O` from [hello.nix](../nix/hello.nix): Hello
2.12.3, its configured gnulib, `-O`, and combined checks (the default).
Hello's source tarball has SHA-256
`0d5f60154382fee10b114a1c34e785d8b1f492073ae2d3a6f7b147687b366aa0`.
The flake lock pins nixpkgs and the Fil-C staging toolchain/runtime.

From the repository root:

```sh
python3 nanofil/tests/watch.py --label trap-census --warn-after 600 --timeout 1800 -- \
  nix build --impure -f nanofil/bench/trap-census.nix -o /tmp/trap-census -L
```

[trap-census.nix](../bench/trap-census.nix) imports the real
`hello.nix` configuration, retaining configure, build flags, link and
tests. It instruments the existing CC wrapper to keep **all 81 objects**,
their actual preprocessed `.i`, optimized `.ir`, and checked `.term`.
It does not compile a glob of pristine C sources: configure-selected
sources, macros and wrapper choices (`$copies`, `$inline`) matter.
The original object compile still goes through nanofil. The retained
checked term uses the same combined pipeline, including its Prolog
validation and refinement gates; already optimized IR is not optimized
a second time. Pointer-free, data-only and empty objects are retained,
even though the `outcomes` command refuses a plain module.

The build reported `nanofil compiled 81 of 81 objects`, matched filcc
on all 12 invocations (also with `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`), and
ran `make check` in both modes: each had 6 passes, 1 NLS skip, no failures.
NLS is deliberately disabled by the pinned derivation, not by this census.

The output contains `hi/`, `hello/build/`, `hello/residual.log`,
`hello/obligations.pl`, each `.term.valid`, both dynamic-symbol
inventories, and `bin/census-valid`. To repeat the queries independently:

```sh
export SWIPL=/path/to/swipl
mapfile -t terms < <(find -L /tmp/trap-census/hello/build -name '*.term' | sort)
nanofil/bin/nanofil --script nanofil/bench/residual.pl --sites-only "${terms[@]}"
nanofil/bin/nanofil --script nanofil/bench/trap-census.pl "${terms[@]}"
for term in "${terms[@]}"; do
  echo "$term"
  /tmp/trap-census/bin/census-valid <"$term"
done
```

Repeat for `hi/` to obtain the smaller census. The query emits every
site's object, function, block, instruction index and IR; Campaign 0's
query additionally emits its shape, loop tag and C provenance.
`--sites-only` preserves Campaign 0's classifications but omits its
native instruction-cost estimator: Hello has 114 named-local checks
that that Lua-calibrated estimator does not support. No invented cycle
cost is assigned, and no sites are dropped to make it run. Its
independent class-`a` count must equal the number of classified sites.

## Residual class-`a` checks

Counts are static sites in every compiled object, **not executions**
and not just the archive members pulled into the final executable.

| Form | `hi.c` | Hello | Obligation remaining |
| --- | ---: | ---: | --- |
| Full `check` | 0 | 524 | range, rights, alignment, lifetime |
| Named-local `check_local` | 0 | 114 | local-range check; do not silently discard it |
| `half_check(lower, ...)` | 0 | 56 | lower bound and flags; other evidence persists |
| `half_check(upper, ...)` | 0 | 344 | upper bound and flags; other evidence persists |
| `renew` | 0 | 360 | flag-only retest: purely temporal, not another bounds proof |
| **Total** | **0** | **1,398** | |

There are 760 reuse retests: 400 half checks and 360 flag-only renewals.
The renewals are 25.75% of all sites. No hull, conditional-renew,
limit or ahead forms occur in this combined-mode capture. A renewal
must establish that the object was not freed; any required write
permission is already justified by the earlier evidence and the stable
read-only flag. A half check still has a spatial obligation as well.

Campaign 0's mutually exclusive shape classification gives:

| Shape | Hello sites |
| --- | ---: |
| Static allocation root | 585 |
| Parameter | 304 |
| Named local | 114 |
| Static global | 110 |
| Mixed roots | 77 |
| Call result | 76 |
| Pointer chase | 68 |
| Dynamic/external global | 63 |
| Allocation, dynamic offset | 1 |
| Integer-derived / other | 0 |

The two allocation-root rows count **checks on pointers derived from
allocations**, not allocation sites. Allocation refusal (`too_big`,
out of memory) and stack overflow are not panic obligations.

610 sites are in natural loops: 24 syntactically affine candidates
(18 full, 4 lower-half, 2 upper-half), of which 5 have a visible
parameter bound, plus 586 other-loop sites. These tags prove neither
no-wrap nor bounds. Of the renewals, 258 are in loops and 102 outside.
The nearest-event tag finds 35 after a call, 12 at a poll edge, 115
after another check, and 198 with no such local event; this is not an
all-path causality analysis. In particular, do not count just the 47
call/poll-tagged sites as temporal: **all 360 renewals are temporal**.

## Frees, function pointers and variadics

| Site kind | `hi.c` | Hello |
| --- | ---: | ---: |
| libc `free` | 0 | 23 |
| Calls through pointer temporaries / explicit `check_function` | 0 / 0 | 0 / 0 |
| `va_args` entry snapshot | 0 | 2 |
| `va_arg` | 0 | 5 |
| Variadic libc call | 0 | 36 |
| Calls of Hello's own variadic functions | 0 | 4 |

Free needs null or a live heap allocation base not already freed.
`realloc`/`reallocarray` additionally impose that condition on the old
pointer and invalidate aliases when they move/free it; their allocator
aspect is not a separate panic obligation.

The snapshots are in `rpl_fcntl` and `version_etc`; the `va_arg` sites
are four in `rpl_fcntl` and one in `version_etc_va`. The external
variadic calls are `fprintf` 17, `fcntl` 9, `error` 5, `printf` 3,
`sprintf` 1, `wprintf` 1. Internal calls are `rpl_fcntl` 3 and
`version_etc` 1. `fcntl`'s argument shape is selected by its command,
not a format string. The five `va_arg` operations also read/write a
cursor and need its memory and lifetime preconditions, beyond the
argument snapshot's size/type contract.

No pointer-call instruction occurs, but this does **not** remove
callback obligations: `atexit` is lowered to `__cxa_atexit`, which
retains a function pointer and calls it during exit. That trusted
contract must constrain signature, argument and callback lifetime,
and compose with `close_stdout`'s own obligations.

For `hi.c`, the body has exactly one direct call, `puts`, and no
class-`a`, free, indirect-call or variadic sites. Its remaining libc
precondition is a readable string containing a NUL within its object:
the retained data is the six bytes `hello\0`. `puts` and the startup/
exit path remain trusted contracts, not a claim of zero obligations.

## Libc contract inventory (correcting the sketch's 66)

The pinned nixpkgs stock `hello-2.12.3` has **64** dynamic-symbol rows:
**61** GLIBC-versioned symbols (including weak `__cxa_finalize`), plus
weak `_ITM_deregisterTMCloneTable`, `_ITM_registerTMCloneTable` and
`__gmon_start__`. Thus the sketch's **66 is not reproducible at this
pin**. Data symbols and startup hooks are not ordinary libc calls.
All 61 stock GLIBC symbols are partitioned below; these are contract
requirements to formalize and probe, not contracts proved by the census.

| Kind (count) | Stock symbols | Required contract |
| --- | --- | --- |
| Byte/string regions (13) | `strlen`, `strnlen`, `strchr`, `strrchr`, `strcmp`, `strncmp`, `memchr`, `memcmp`, `memcpy`, `memset`, `strdup`, `__memcpy_chk`, `__mempcpy_chk` | Read/write authority, in-object NUL or bounded byte count, pointer-result provenance. Copy requires nonoverlap where specified; fortified variants also require the destination object-size bound. `strdup` returns fresh owned storage or null. |
| Heap lifetime (4) | `malloc`, `calloc`, `realloc`, `free` | Fresh owned allocation or refusal; `calloc` multiplication/refusal behavior; realloc/free take null or a live owned heap base. Reallocation success and failure have different ownership postconditions. |
| Formatted output and streams (10) | `__printf_chk`, `__fprintf_chk`, `__sprintf_chk`, `__wprintf_chk`, `fputc`, `fputs`, `error`, `fclose`, `ferror`, `__fpending` | Live stream where required; readable format and strings; matching varargs; `%n` needs writable destination. `sprintf` needs sufficient output capacity; fortification adds size/format restrictions. Closing consumes stream lifetime; I/O failure is a result, not a panic. |
| argv parsing (3) | `getopt_long`, `optarg`, `optind` | Well-formed argv, readable option strings and sentinel-terminated option table; writable option-index output when supplied. State mutation and returned pointers into argv must be specified. |
| Locale/characters (13) | `setlocale`, `nl_langinfo`, `bindtextdomain`, `textdomain`, `dcgettext`, `__ctype_b_loc`, `__ctype_get_mb_cur_max`, `mbrtowc`, `mbrtoc32`, `mbsinit`, `iswalnum`, `iswprint`, `iswspace` | Valid category/item and character domains; readable string arguments or documented null queries; returned-table/string bounds and invalidation at locale changes. `__ctype_b_loc` covers indices −128 through 255. Multibyte conversions need bounded input, writable output/state and initialized or valid conversion state, including null/reset cases. |
| Conversion descriptors (3) | `iconv_open`, `iconv`, `iconv_close` | Encoding strings; successful live descriptor; readable/writable pointer-and-length cells and the ranges they designate. Include reset/flush null cases, cursor updates, partial conversion/error results and close lifetime. |
| Process endings/failures (5) | `exit`, `_exit`, `abort`, `__assert_fail`, `__stack_chk_fail` | End-of-trace behavior, readable diagnostic strings for assert; `exit` invokes registered handlers. `__stack_chk_fail` is an instrumentation failure path, not an ordinary call to justify away. UB and unreachable remain ruled out, not vacuous success. |
| Startup and callbacks (3) | `__libc_start_main`, `__cxa_atexit`, `__cxa_finalize` | Entry argv/environment and initial readiness, function signatures, callback arguments, registration lifetime and execution at exit/unload. |
| Exposed state (7) | `stdout`, `stderr`, `__errno_location`, `__progname`, `__progname_full`, `program_invocation_name`, `program_invocation_short_name` | Stream object capabilities, writable thread-local errno cell, readable NUL-terminated program names, aliasing and lifetimes. These are data/getter contracts, not seven more formatted-output calls. |

The **actual nanofil executable** has 82 dynamic rows, one a defined
weak symbol: 81 imports, of which 58 rows are GLIBC-versioned. Those
58 are 55 `pizlonated_` symbols plus native startup's `abort`,
`__libc_start_main` and weak `__cxa_finalize`. Stripping `pizlonated_`
and deduplicating gives **56 libc names**, not 58 independent contracts.
The complete raw inventories are retained by the reproduction above.

Compared with the stock table, those 56 names omit
`__fprintf_chk`, `__memcpy_chk`, `__mempcpy_chk`, `__printf_chk`,
`__progname`, `__progname_full`, `__sprintf_chk`, `__stack_chk_fail`,
`__wprintf_chk`, `bindtextdomain`, `dcgettext`, `fputc`, `textdomain`;
and add `fprintf`, `iswcntrl`, `mempcpy`, `printf`, `reallocarray`,
`sprintf`, `wcwidth`, `wprintf`. Apply the same nine contract kinds:
unfortified output loses the `_chk` size parameter, not its buffer
obligation; `mempcpy` returns the destination end; `reallocarray`
adds multiplication/refusal behavior; wide-character predicates and
`wcwidth` have character-domain requirements.

Other imports are runtime/ABI support, including `pizlonated_zmemmove`
(overlap-safe region-copy contract), allocation and barrier/check/poll
helpers, and native weak frame-registration hooks. They are not 23
additional libc APIs. All-object sites include archive members the
linker does not pull, notably the nine `fcntl` calls: that contract
requires a command-appropriate optional argument, live descriptor,
and authority over any pointed-to structure. Do not equate the
all-object call inventory with final executable dynamic imports.

## Direct extracted validator results

| Program | Objects | Functions inside / outside | `Validate.valid` |
| --- | ---: | ---: | --- |
| `hi.c` | 1 | 1 / 0 | 1 × `Some true` |
| Hello, every compiled object | 81 | 178 / 0 | 81 × `Some true` |

**No Hello function is outside the current model's subset.** Empty
and data-only objects are included. This is decoding and validation,
not execution: externals other than `free` are still stuck in the run
semantics and need Campaign 4 contracts. It establishes neither
cross-object linking correctness nor `never_panics`.

The ordinary `nanofil-model --valid` interface calls `judge_valid`,
which can give per-item judgments with outside functions present.
To answer the stronger whole-object question, this census additionally
extracts the existing option-valued `Validate.valid` through `rocq repl`,
using the flake's Rocq environment, without changing any `.v` file.
[trap-valid.ml](../bench/trap-valid.ml) calls that function directly and
lists every decoded `IFunc`/`IOutside`; `None` is not treated as success.

Running Hello exposed a reader bug, not a validator disagreement:
SWI emits bare `;` and `!` atoms inside data `str` lists, but the
extraction driver's parser did not accept them. The driver now accepts
both, with [strings.ir](../rocq/tests/strings.ir) as a regression.
No Gallina/model verdict was changed to get Hello accepted.

Next is still Campaign 7's closed-module proof (step 1), and Campaign
4's external-call/trace contracts before `hi.c` (step 2). This census
does not prove UB/unreachable absent, discharge any checks, link the
81 modules in Rocq, or supply the native libc-contract probe suite.
