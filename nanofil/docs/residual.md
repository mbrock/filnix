# Campaign 0: Lua's residual checks

November 2026. **Keep Campaign 5 before the ownership inquiry, but start
with a small spatial-discharge case, not a claim that Lua is mostly affine
loops.** Flag-only renewals are 24.49% of the static residual; 75.51%
still test at least one bound. Static counts do not establish which
class dominates execution time.

## Input and counting unit

Measured with the compiler at
[`e57baab5e575`](https://github.com/mbrock/filnix/commit/e57baab5e57559c76361628c637e10824dd253f5),
using SWI-Prolog 9.2.9 and staging Fil-C 0.687 for preprocessing. No
compiler, validator, runtime or Rocq code changed for this measurement.

The corpus is **all 34 C translation units of Lua 5.4.7**, including the
`lua` and `luac` drivers: 769 function definitions after optimization,
counted per translation unit, not a linked executable. The source is
the pinned nixpkgs `lua5_4.src`, also used by [nix/lua.nix](../nix/lua.nix).
Its tarball SHA-256 is
`9fbf5e28ef86c69858f6d3d34eccc32e911c1a28b4120ff3e84aaa70cfbf1e30`.
Preprocessing uses `-O2 -std=gnu99 -DLUA_USE_LINUX
-DLUA_USE_JUMPTABLE=0 -U__SIZEOF_INT128__ -E`. The middle end uses
nanofil `-O`, including its default wide inlining and full simplification;
the checked stage uses `--checks=combined`.

The counting unit is a **static explicit data-access check site** (a
class-`a` instruction), not an access, a dynamic execution count or a
runtime call. Reuse can serve several accesses with one site. The census
includes 10,353 sites, including `luaD_rawrunprotected`; it is not the
Rocq-decodable subset. Separately, there are 58 `check_function`
instructions. Poll tests, allocation checks, pointer aux operations,
opaque runtime checks inside `setjmp`/variadics, and the function checks
are outside the data-access histogram.

## What survives combined checking

| Check form | Sites | Share | Estimated core cycles per execution |
| --- | ---: | ---: | ---: |
| Full `check` | 4,454 | 43.02% | 1.95 |
| `half_check(lower, ...)` | 1,582 | 15.28% | 1.09 |
| `half_check(upper, ...)` | 1,782 | 17.21% | 1.16 |
| Flag-only `renew` | 2,535 | 24.49% | 0.42 |
| **Total** | **10,353** | **100%** | |

These are the only class-`a` forms in the measured corpus. In particular,
combined emits no `span_test` or `renew_if` here: it is forward reuse,
renewal and half checking, not the optional loop-guard mode.

### Pointer shape, independently of check form

This is a disjoint histogram. Follow a flight's **capability donor**, not
its address bits; traverse pointer phis and retain root identities. Two
distinct loaded pointers remain different roots even if both are loads.
Mixed roots take precedence over every single-root category. A global or
constant-size allocation is classified as static only if the address has
a constant offset from that root; a static classification is not a proof
that the offset is in bounds or that the object is live.

| Pointer shape | Full | Half lower | Half upper | Renew | Total | Share | Estimated core cycles/execution |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Function parameter, including derived addresses | 926 | 933 | 746 | 1,210 | 3,815 | 36.85% | 1.10 |
| Pointer chasing: root is a `raw_load_pointer` result | 1,947 | 250 | 485 | 615 | 3,297 | 31.85% | 1.47 |
| Constant-offset, constant-size allocation | 539 | 98 | 133 | 426 | 1,196 | 11.55% | 1.26 |
| Phi with multiple root identities | 372 | 196 | 255 | 141 | 964 | 9.31% | 1.30 |
| Call result | 331 | 101 | 146 | 140 | 718 | 6.94% | 1.41 |
| Global with dynamic offset or external definition | 162 | 1 | 0 | 0 | 163 | 1.57% | 1.98 |
| Constant-offset global defined in this unit | 114 | 0 | 5 | 1 | 120 | 1.16% | 1.93 |
| Constant-size allocation, dynamic/unresolved offset | 53 | 3 | 4 | 2 | 62 | 0.60% | 1.80 |
| Other/unresolved | 10 | 0 | 8 | 0 | 18 | 0.17% | 1.73 |
| Integer-derived/laundered capability | 0 | 0 | 0 | 0 | 0 | 0% | — |
| Named-local `check_local` | 0 | 0 | 0 | 0 | 0 | 0% | — |

The 18 other/unresolved sites stay in the denominator. A phi that keeps
one allocation's identity but selects different offsets belongs in the
dynamic-offset row, not the constant-offset row. No `flight` in the
corpus has `none` authority or different address and capability donors;
the zero integer-derived row is an observation of this corpus, not a
claim that C casts cannot occur. Named-local operations without an
explicit check are not surviving check sites.

### Loop and safepoint tags overlap the pointer histogram

Of the sites, 3,459 (33.41%) are in natural loops. The query recognizes
279 (2.69% of all sites) whose address has a syntactically affine
scalar-induction component; 12 also have a comparison with a visible
scalar parameter in the same loop. The other 267 have no such recognized
comparison. This finder handles constant scale/shift, addition,
subtraction and integer extension of an induction phi with a nonzero
constant recurrence. It does not solve pointer induction, bounds loaded
from Lua objects, arbitrary invariant expressions, wrapping arithmetic,
or path conditions. **These are candidates, not 279 certificates, and
the unrecognized sites are not proved non-affine.** A nearby parameter
comparison does not establish that the parameter describes the accessed
object's extent or controls the access on every path.

| Loop tag | Full | Half lower | Half upper | Renew | Total |
| --- | ---: | ---: | ---: | ---: | ---: |
| Affine candidate with visible parameter comparison | 9 | 0 | 2 | 1 | 12 |
| Other recognized affine candidate | 212 | 13 | 25 | 17 | 267 |
| Other loop site | 1,289 | 400 | 524 | 967 | 3,180 |
| Outside natural loops | 2,944 | 1,169 | 1,231 | 1,550 | 6,894 |

For the temporal question, **all 2,535 renewals** already test flags
without rechecking bounds or alignment (writes also test read-only).
Of them, 288 are the first explicit data check after a call in the same
block, and 145 are the first check in a block with an incoming poll
edge: 433 sites, 4.18% of the census. This is a deliberately narrow
syntactic tag, not an all-path or per-object safepoint analysis. The
remaining 2,102 renewals must not be called non-temporal just because
they lack that tag. Conversely, a full check after a call still has
spatial obligations and is not classified as flag-only.

Examples recoverable from the site's provenance: `lua_checkstack` in
`lapi.c:115` starts with a parameter-root check; `luaZ_fill` in
`lzio.c:34` includes a pointer-chasing check; `luaZ_read` in `lzio.c:61`
has a post-call renewal. Provenance includes enclosing locations, not
an exact source-expression span, so each output row retains all its
reachable source locations rather than choosing an arbitrary one.

## Cycle estimates, not new hardware measurements

The tables estimate only the successful **check core**. The query
counts the existing x86-64 emitter's split-bounds sequences with local
selection, before check sharing: 8–12 instructions for a full check,
4–6 for half lower, 4–8 for half upper, and 2 for renewal. Counts include
the relevant write and alignment tests. Pointer preparation, the access,
aux lookup, calls, polls, failure reporting and cache misses are excluded.
Sharing can remove more instructions, so these are unshared code-cost
estimates, not a count of the final executable's instructions.

The conversion is **0.21 cycles per instruction**, the explicitly
inferred native-gate conversion in [perf.md, item 19's “Levers, ranked” table](perf.md).
For each row, sum its core instruction counts, divide by its static site
count, then multiply by 0.21. For example, full checks have 41,340 core
instructions over 4,454 sites: 41,340 / 4,454 × 0.21 = 1.95 cycles.
This is an equal-site average, **not a hotness-weighted average**.
Renewals contribute 5,070 of 64,422 core instructions (7.87%) under the
same artificial one-execution-per-site weighting, not 7.87% of Lua time.

No new native Lua benchmark was run for this document. The calibration
comes from the native benchmark record, not the orb's wall clock. Its
CPU/workload aggregate is not a latency model for this Xeon orb, a
dependent pointer chase, a cache miss or a mispredicted branch. The
benchmark record also documents layout-sensitive slowdowns despite
instruction savings. To decide actual savings, use the Lua `int`, `tab`
and `str` workloads in [bench/run.py](../bench/run.py), collect dynamic
site weights and native cycles, and compare a validated discharge with
the unchanged combined build. Static site counts alone cannot supply
per-workload cycle totals or an end-to-end speedup prediction.

## The query and reproduction

The complete read-only query is [bench/residual.pl](../bench/residual.pl).
Its top-level census is:

```prolog
maplist(file_sites, Files, Groups), append(Groups, Sites).
```

Each row is
`site(File, Function, Block, Index, Form, Shape, LoopTag, AfterTag, Locations, CoreInstructions)`.
`count` facts give each histogram and the form/shape cross-tab;
`instructions` facts give summed core counts. Every class-`a` instruction
is independently counted again; a missing classification fails the
query instead of shrinking the denominator. Unsupported core forms fail
rather than receiving a guessed cost.

The query uses `ir:single_definitions/3`, `ir:pointer_distance/4`,
`cfg:natural_loops/3`, `provenance:context_records/3`,
`provenance:site_index/2` and `provenance:site_origins/3`. It follows
`origin` parents to C locations. All 10,353 sites have source locations.
The core costs come from the emitter's existing DCGs, not a duplicate
implementation of their instruction counts.

From the repository root, after the tool builds in `nanofil/AGENTS.md`:

```sh
export SWIPL=/tmp/swipl/bin/swipl FILCC=/tmp/filcc/bin/clang
nix build -o /tmp/lua-source --impure --expr \
  '(import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }).lua5_4.src'
work=$(mktemp -d)
mkdir "$work/lua" "$work/checked"
tar -xf /tmp/lua-source -C "$work/lua" --strip-components=1
nanofil/bin/nanofil --save-state "$work/nanofil.state"
export NANOFIL_STATE="$work/nanofil.state"
for c in "$work"/lua/src/*.c; do
  b=$(basename "$c" .c)
  python3 nanofil/tests/watch.py --label "residual-$b" -- bash -c '
    "$FILCC" -O2 -std=gnu99 -DLUA_USE_LINUX -DLUA_USE_JUMPTABLE=0 \
      -U__SIZEOF_INT128__ -E "$1" -o "$2.i" &&
    nanofil/bin/nanofil -O cc-ir "$2.i" > "$2.ir" &&
    nanofil/bin/nanofil --checks=combined outcomes "$2.ir" > "$2.term"
  ' _ "$c" "$work/checked/$b" || exit 1
done
python3 nanofil/tests/watch.py --label residual-query -- bash -c '
  nanofil/bin/nanofil --script nanofil/bench/residual.pl "$1"/*.term > "$2"
' _ "$work/checked" "$work/sites.pl"
tail -1 "$work/sites.pl" # total(34,10353).
```

The separate `cc-ir -O` step preserves C inlining attributes; the next
step only pizlonates and applies combined checking, without running the
middle end twice. Do not feed `.i` directly to `outcomes`: it currently
tries to read IR run facts from the C input after printing the module.
Absolute source paths in provenance vary with the extraction directory.

Validation also used a separate C control corpus: distinct-parameter
phis versus different offsets of the same parameter, a pointer load,
an integer cast, a static global, an indexed loop bounded by a parameter,
and a load/call/reload. This caught a missing constant-shift case in the
initial loop finder. Additional controls distinguish a nonlinear index
from an affine one, and a phi's shared allocation/global identity from
its variable offset. The final finder recognizes the affine loop, keeps
the same-root phi out of the mixed-root bucket without calling its offset
constant, and tags the reload as a 2-instruction post-call renewal. No
transformation or discharge is authorized by this query.

**Decision: Campaign 5's spatial-certificate pilot comes before the ownership inquiry; revisit that ordering with dynamic weights, not a claim that the residual is mostly affine loops.**
