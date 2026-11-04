# Forward facts: check evidence kept as filcc's forward pass keeps it

Status: part of the `-O` default since perf.md item 18
(`--checks=combined`, which runs half checks after it; alone,
`--checks=forward`, November 2026). No trap moves: every check that remains is
its access's own reference check, at its place, and every deleted check
is one that would have passed.

perf.md item 16 measured that moving traps earlier (filcc's backward
propagation, [schedule.md](schedule.md)) accounts for only 82M of the
627M executed-check gap to filcc -O2, and that most of what is
reachable is filcc's *forward* rule, `removeRedundantChecksUsingForwardAI`
(FilPizlonator.cpp, around line 5770). Its candidate 1 is this: keep
facts where filcc keeps them, for pointer uses too, and let the hull of
several earlier checks of one object cover a later one.

## What filcc's forward rule keeps

Requirements are keyed by canonical pointer (base plus constant offset)
and kind. Walking forward, a check whose requirements are all known is
deleted; one whose bounds are known keeps only its unknown kinds.

| Event | Ends |
|---|---|
| a back edge's pollcheck | `NotFree`, `GetAuxPtr` |
| a call that may write memory, an alloca that may exit (`instructionMayFree`) | `NotFree`, `GetAuxPtr` |
| an `EnsureAuxPtr` (a pointer store) | `NotFree`, other pointers' `GetAuxPtr` |
| a redefinition (SSA: none) | its pointer's facts |

Bounds and alignment facts survive everything. Merges at joins meet
(intersect; bounds take the weaker), iterated to a fixpoint. Bounds
facts of one canonical base at different offsets combine: an object is
one interval, so two checked fields span what lies between.

## What nanofil already had

M7 ([m7.md](m7.md)) keeps two kinds of evidence:

- **live facts** `live(Q, P, Lo, Hi, Rights, Align)` (rounds 1–3): a
  later scalar access may read proof Q without any test, while only
  `evidence_preserving/1` instructions and plain edges come between.
  This is filcc's bounds plus `NotFree`.
- **renew sources** (round 4): a dominating single-definition check's
  bounds and alignment hold forever, so a later check becomes a flag
  test. This is filcc's bounds facts surviving calls and polls, with
  `NotFree` (and `CanWrite`) tested again.

Item 16 found the gap in three places: a pointer access never read a
live proof (only scalar accesses did); a live proof covered only its
own range, so `s->b` after `s->a` and `s->p` was checked in full; and
renewal needed distance 0.

## nanofil's rule

`--checks=forward` = reuse in mode `forward`, then renewal at any
distance. Three changes, none to the IR grammar:

1. **Pointer loads read live proofs.** A `raw_load_pointer` with the
   heap load effects (aux and box reads, no helper) may read a live
   proof that covers it, as a scalar access may. A pointer store keeps
   its own check: its ensure-aux may exit, as filcc's `EnsureAuxPtr`
   ends `NotFree`. A cas keeps its own (atomic).
2. **The hull.** A raw access through a live proof Q of P is covered
   when the live facts of P's object together span it: facts whose
   pointers lie at exact distances from P through one single-definition
   base. Each says its bytes were inside the object at its check; all
   are live, so the object has not been freed since; an object is one
   interval. A write needs one of them with write rights (read-only is
   the object's flag). Alignment is Q's own fact's, relative to its
   lower end, as for a plain reuse. Every offset, distance and span end
   counts only within ±2^62, where the integers are the true distances
   (pointer arithmetic wraps; [schedule.md](schedule.md)'s review found
   this). A function with a setjmp has no hull, in the validator or the
   pass.
3. **Renewal at any distance** (`renew_checks(any, …)`), the rule
   [schedule.md](schedule.md) added: a check whose range a dominating
   check of a related pointer covers, shifted by their distance, tests
   only the flags.

What ends a live fact is unchanged (m7.md's invalidator list): a call,
`alloc`, a getter, a pointer store, setjmp, va_arg, a poll edge, an
edge from a later block, a redefinition.

## Checked-IR evidence and the validator rule

No new term. ir.pl's generic `checked_inst_rest` clause accepts a raw
access at proof Q when `reusing_access/2` admits its kind (scalar, or a
heap pointer load) and Q's live fact covers it (`covered_access/6`, as
before) or `hull_covered/7` holds. The validator recomputes the live
facts by its own dataflow (`checked_block`, `evidence_after/3`) and
the relation of pointers by `pointer_distance/4`, independent of the
pass's `base_of/4`. `stage_sources` now computes `single_definitions/3`
for every function without a setjmp (with one, no hull).

## Interpreter rule

Unchanged. A raw access is tested against its proof's capability as
the object is now: a hull that did not hold, a freed object or a
missing write right shows as `unchecked(Why)`, which refines nothing.
As for M7, the interpreter models explicit frees only; polls,
allocation exits and ensure-aux are covered by the invalidator list and
the native GC tests.

## Emitter rule

`fused_insts` treats a standalone heap pointer load at a proof as
`reused(Access)`, like a scalar one. `inst(reused(...))` loads the full
pointer pair for it (`flight_load`), since the aux read needs the lower
in %rcx, adds the offset, and performs the load with no check.
Liveness reads P, so P stays rooted until its last reused access.

## The pass

`check_reuse:reuse_checks/3` with `forward`: `reuse_access/3` admits heap
pointer loads (and their own checks make facts); `covering/9` tries
the subsuming fact first, then the hull of the root's available facts
with the nearest reader whose alignment suffices, within the 32-bit
offset a reused access emits with. `reuse_refines/3` checks identity
(same operand or a related one at its distance) and, independently of
the validator, that the deleted check would have passed: either the
reading proof's check subsumes it, as before, or the deleted check is
exactly its access's requirement (`own_requirement/5`, as pizlonation
makes every check), so the validator's accepting the access implies it.
Coverage is the validator's question. Renewal is `renew_checks(any, …)` with
`renew_refines/3`.

## Tests and plants

- `tests/unit.pl`: `forward_validation` (a hull of two fields; one side
  only; a call between; another object's wide fact; a write with read
  facts only, then with one write fact; a wrapped offset; a pointer
  load through a hull; a pointer load whose reading proof's alignment
  is too small), `forward_pass` (plain reuse keeps the hull field and
  the second pointer load, forward deletes both; outcomes agree; after
  a free nothing is deleted and the run traps as the reference), and
  `reuse_validation`'s pointer cases (a heap pointer load at a live
  proof accepted, a pointer store rejected).
- `tests/c/prog/forward-free.c` in `tests/renew-trap.sh`: the forward
  build has fewer check tests than the renew build, prints the same sum
  before the free, and traps after it with the reference build's whole
  stderr.
- nix/check.nix runs difftest, ABI+GC and progtest with and without
  `-O`, and the corpus under `-O`, all with `NANOFIL_CHECKS=forward`.

Plants, each caught and restored (with the review's four below): the hull without the ±2^62 bound,
without rights, relating any fact regardless of object, needing only
the lower side, or ignoring alignment (forward_validation fails, some
also reuse_validation and reuse_related); a pointer store reading a
live proof (reuse_validation); the emitter loading only the address
for a reused pointer load (renew-trap.sh: forward-free crashes).

## Review (November 2026)

A reviewing subagent attacked the validator rule, the pass, the
emitter and trap preservation. It found nothing reachable from C that
changes safety or moves a trap, and four problems, all fixed, each with
a test that fails without the fix:

1. **Unsound for hand-written IR: a fact's own range wrapped.**
   `hull_covered/7` bounded the access and the distance but not each
   fact's `Lo1`/`Hi1`, so `check(2^64+8, 2^64+12)` (P+[8, 12) modulo
   2^64) spanned past P+1000. Fixed by `near_offset/1` on the span ends
   (forward_validation's last case). Pizlonation and the emitter only
   make checks at offset 0 of at most 2^31 bytes, so no compiled
   program was affected.
2. **Compile failure from C: a far reader.** The pass took the first
   fact whose alignment sufficed, which could be 2^32 away
   (`p[0]; p[0x100000000L]; p[5]`), and the emitter refused the offset.
   Fixed: the nearest reader within 32 bits
   (`tests/c/prog/reach-far.c`, in progtest).
3. **Validator rejection: setjmp.** The validator has no hull with a
   setjmp; the pass did. Fixed: the pass's mode there is pointer loads
   only (forward_pass's setjmp case).
4. **Trap preservation not checked independently.** `reuse_refines/3`
   skipped subsumption entirely in forward mode, so a deleted check
   wider than its access (which would have trapped) passed refines and
   the validator. Fixed by `own_requirement/5` (forward_pass's last
   case).

Found sound: object bounds are one interval changed only by free
(`upper` is written at allocation and by `free_impl`, which also sets
the FREE flag; special objects have zero size); the same capability
means the same object; read-only is set only at allocation, so one
write fact covers every related pointer; alignment relative to the
lower end equals absolute alignment (objects are 16-aligned); a reused
pointer load needs nothing a fused check leaves in registers
(`aux_read` reloads the aux word itself; a scalar fact's alignment 1
can never serve a pointer load's 8); single-definition bases under
strict SSA with back edges carrying no facts; the emitter's offset add
and P's rooting; no trap is added, lost or reordered. It also built all
187 runnable `tests/c/prog` programs with renew and with forward:
stdout, exit status and safety-error text matched, and jumps to failure
blocks fell from 47597 to 46799.

## Measurements (November 2026)

Executed checks on the gate (callgrind, perf.md item 16's
`bench/profile/checks.py`, the same count as its ladder), millions;
full checks are those with a null test:

| Workload | checks, O → forward (filcc) | full checks, O → forward | check instructions, O → forward |
|---|--:|--:|--:|
| zlib -6 | 241.0 → 193.5 (136.2) | 165.9 → 140.3 | 1299 → 1078 |
| zlib -d | 17.6 → 17.5 (11.7) | 17.3 → 17.3 | 131 → 130 |
| bzip2 -9 | 512.8 → 470.2 (332.9) | 381.1 → 373.5 | 2909 → 2823 |
| bzip2 -d | 118.1 → 109.0 (86.2) | 82.9 → 82.9 | 660 → 653 |
| lz4 -9 | 155.8 → 151.3 (116.2) | 138.1 → 135.5 | 1062 → 1040 |
| lua int | 68.1 → 64.1 (48.0) | 62.0 → 60.0 | 484 → 468 |
| lua tab | 60.2 → 54.2 (38.1) | 54.1 → 52.1 | 425 → 407 |
| lua str | 85.8 → 82.7 (59.5) | 74.1 → 73.7 | 629 → 623 |
| sqlite | 557.9 → 521.7 (364.7) | 456.6 → 439.8 | 3725 → 3568 |
| **all** | **1824 → 1671 (1197)** | **1439 → 1382** | **11373 → 10840** |

So −153M checks of the 627M gap (item 16 estimated −271M), −57M full
checks and −0.53G check instructions (estimated −1.2G); program
instructions 52.9G → 52.2G. bzip2's copy_input_until_stop: 121.5M →
90.1M. zlib's deflate_slow: 98.0M → 61.1M.

Time, `run.py --modes ref,O,O-forward`, 5 trials on cpu 6 after waiting
for a quiet core: geomean ratio to filcc -O2 1.82 → 1.80 (instructions
2.80 → 2.77); zlib -6 2.09 → 2.06, lua tab 1.44 → 1.41, the rest within
the trials' spread.

Where the estimate's remainder is: getters end every fact (the largest
case seen, a `BZ2_crc32Table` getter in copy_input_until_stop's loop
body), and the 100M of item 16's covered class that are full checks
covered by a hull become deletions only when their facts are live;
where a call separates them they need a renew with several sources.

## Getters (November 2026)

Opt-in as `--checks=getter` (forward facts, then renewal and half
checks, as `combined`) and, with the next section, `--checks=extended`.

**What a getter may do.** `let(tmp(D), p, copy, [global(G)])` calls
`pizlonated_G(thread, origin)` (abi-findings.md, Globals). Read in
staging's `filc_runtime.c` and FilPizlonator.cpp:

- *Fast path:* load the two cache words `GP_G`; if both are nonzero,
  return them. No call, no store, no safepoint. Thread-local getters
  read their `.tbss` slot the same way.
- *Slow path:* `filc_global_initialization_start` sets the frame's
  origin, checks the stack limit (it may trap), and takes the
  initialization lock with `filc_lock_lock`. Under contention that calls
  `filc_exit`, which runs deferred signal handlers
  (`handle_deferred_signals`, filc_runtime.c:1243): arbitrary user code,
  which may free, store pointers or run the collector. The initializer
  then runs constant relocations, which call other getters. An ifunc's
  getter calls `filc_call_ifunc`, which runs the resolver, user code. A
  thread-local getter's slow path allocates, which is a safepoint.

So a first getter call can reach arbitrary code. `tests/c/getter`
shows it: an ifunc resolver frees the object whose fields `g` reads
around `&f`. Reference nanofil and filcc -O0 trap on the read after the
getter. filcc -O2 does not: its scheduleChecks runs before getter calls
exist (FilPizlonator.cpp:17591, then optimizeGetters at 17865), so it
treats the global's address as free of effects.

**Rule.** A getter copy of G keeps every live fact when another copy
of G dominates it (an earlier one in its block, or one in a strictly
dominating block) and G is a function or data item this module defines
with local linkage (`local`, `ro(local)`, `tls(local)`). Its
destination's facts end, as for any definition. The getter is then the
one nanofil emits for G, a local symbol no other module can interpose,
and a call of it has returned in this activation on this thread:

- a data getter has published its cache, so the fast path runs; or this
  thread is inside an initialization of G's generation, reachable only
  from a signal handler or an ifunc resolver during an initializer. The
  slow path then finds G already seen and returns. It holds the lock
  recursively, so it never reaches `filc_lock_lock`, runs no user code
  and frees nothing;
- a function's getter returns its object without a call;
- a thread-local getter finds this thread's slot set.

Its stack check passed at the first call, and the stack is no deeper.
Another thread's free in between is the tolerated race of every check
and its access.

**Why only local globals** (the review, below). An external or
exported getter may be anything at run time:
- *Null-returning ifunc resolver.* An ifunc whose resolver returns
  null leaves the cache half null, so every call of its getter runs the
  resolver again, user code, even a dominated call.
- *Interposition.* An exported definition's getter can be interposed by
  another module's ifunc.

`tests/getter-trap.sh` builds both external cases (lib.c by filcc) and
a local one:
- The first call of f's getter frees the object, and the read after it
  traps.
- f0's resolver returns null and frees on its second call, so the read
  after a dominated copy of f0 traps too.
- A repeated copy of a static function's address keeps the facts.

Planted, each is caught: keeping facts across every getter (in the pass
and validator both) loses the first trap; dropping the linkage
restriction loses the second (the program prints 0 and exits 0 where
the reference traps).

The validator states the rule in `ir:repeated_getters/4`, read in
`checked_inst_rest/7`. The pass calls the validator's relation, so it
keeps nothing the validator refuses. The interpreter models a getter as
the global's pointer with no effect, so it needs no new rule. The
emitter is unchanged: the getter is still an ordinary call, and every
register it clobbers is restored from homes and frame slots, as
renewal across calls already relies on. Share (perf.md item 17) still
treats the call as opaque.

**Why bzip2 does not gain.** `BZ2_crc32Table` is defined in another
translation unit (crctable.c), and its getter in copy_input_until_stop
is also the first copy in each loop iteration, with no copy before the
loop. Both make it exactly the case that may reach arbitrary code. Keeping facts there would need a fact about the
program's history (the cache published), not about this activation.
That would be the user's decision, and is not proposed.

## Renewal by the hull of two checks (November 2026)

Opt-in as `--checks=hull` (and `extended`). One new IR term, approved:

    let(tmp(Q), a, renew_hull(Lo, Hi, Rights, Align), [tmp(QL), tmp(QH), P])

It is `renew(Lo, Hi, Rights, Align)` of P whose bounds and alignment
come from two earlier heap proofs, so a full check that no single
dominating check covers, but two do, becomes a flag test across calls.
It traps where the check would. After a free, both the check and the
renew fail at the access with the "free object" report. A write to a
read-only object reports "read-only". Its access and report are the
replaced check's.

**Validator** (`hull_renewable/8`). QL and QH are in the renew-source
table: single-definition proofs of check, check_ahead, renew_if,
check_limit or half_check, of single-definition pointers PL and PH, in
a function without setjmp. Their checks passed at points that dominate
this one (strict SSA), and P = PL + DL and P = PH + DH modulo 2^64
(`pointer_distance/4`), so all three have one capability. With

- E = Lo + DL − LoL and F = HiH − Hi − DH both in [0, 2^62], and
- Hi − Lo ≤ 2^62:

P+Lo is E bytes above PL+LoL, which was at or above lower, and P+Hi is
F bytes below PH+HiH, which was at or below upper. Both checks' bytes
lie in one object below 2^56, so those integer sums do not wrap. An
object is one interval, and its bounds change only when it is freed,
which the flag test catches. Read-only is per object. Alignment comes
from either source: Al1 mod Align = 0 and (Lo + D − Lo1) mod Align = 0.

**Interpreter.** `kind_res(renew_hull, ...)` runs the check's whole
access test on P, as renew does. A failure other than free or read-only
is `unchecked(span)`, and a source of another capability is
`unchecked(alias)`.

**Emitter.** It is emitted as `renew` of QL. The flag test reads only
P's lower, so no emitted line is new and no SMT proof changes (half's
and share's are untouched).

**Pass.** `renew_checks(hull, ...)` first runs the single-source
renewal (`any`). Then, in dominator-tree preorder, it turns each check
that no renew reads and that no single source covers into a renew_hull
of two dominating sources (`hull_pair/13`, the validator's bounds),
never reading a check it has already replaced.
`renew_refines(hull, ...)` accepts only checks replaced by renew_hull
of related checks of the same range, rights and alignment.

## Measurements of hull, getter and extended (November 2026)

Callgrind on the gate (`bench/profile/checks.py`). Columns are filcc /
`-O` (combined, share upper) / `--checks=hull` / `--checks=extended`.
`getter` alone matches `-O` within 0.1%, because the gate's only hot
getter is bzip2's extern `BZ2_crc32Table`:

| Workload | checks (M) | check instructions (M) | program instructions (G) |
|---|--:|--:|--:|
| zlib -6 | 136.2 / 171.0 / 173.3 / 173.3 | 703 / 969 / 961 / 961 | 1.95 / 6.42 / 6.41 / 6.41 |
| zlib -d | 11.7 / 16.5 / 16.5 / 16.5 | 56 / 105 / 105 / 105 | 0.18 / 0.54 / 0.54 / 0.54 |
| bzip2 -9 | 332.9 / 461.3 / 462.2 / 462.2 | 1823 / 2355 / 2309 / 2309 | 4.66 / 9.30 / 9.27 / 9.27 |
| bzip2 -d | 86.2 / 109.0 / 109.0 / 109.0 | 417 / 549 / 482 / 482 | 1.41 / 3.73 / 3.68 / 3.68 |
| lz4 -1 | 0.3 / 3.2 / 3.2 / 3.2 | 2 / 23 / 23 / 23 | 0.01 / 0.23 / 0.23 / 0.23 |
| lz4 -9 | 116.2 / 150.5 / 150.5 / 150.5 | 647 / 985 / 985 / 985 | 2.86 / 7.19 / 7.19 / 7.19 |
| lz4 -d | 3.5 / 3.8 / 3.8 / 3.8 | 16 / 27 / 27 / 27 | 0.06 / 0.32 / 0.32 / 0.32 |
| lua int | 48.0 / 52.0 / 52.0 / 52.0 | 258 / 372 / 362 / 362 | 1.22 / 1.95 / 1.94 / 1.94 |
| lua tab | 38.1 / 44.1 / 44.1 / 44.1 | 231 / 327 / 327 / 327 | 0.96 / 1.49 / 1.49 / 1.49 |
| lua str | 59.3 / 66.3 / 67.0 / 67.0 | 418 / 542 / 538 / 538 | 1.92 / 3.11 / 3.11 / 3.11 |
| sqlite | 364.7 / 451.7 / 463.5 / 463.5 | 2015 / 2968 / 2851 / 2851 | 9.50 / 15.67 / 15.58 / 15.56 |
| **all** | **1197 / 1530 / 1545 / 1545** | **6584 / 9221 / 8969 / 8969** | **24.7 / 49.95 / 49.76 / 49.74** |

A renew_hull counts as one check, just as the full check it replaces
did. The extra 16M are checks the classifier counts that the
single-source renewal used to fold into its neighbour; that is a guess,
not verified. Check instructions fall by 252M (2.7%). Most of that is
SQLite (−117M), bzip2 -d (−67M) and bzip2 -9 (−46M).

Time, `run.py --modes ref,O,O-hull,O-extended`, 7 trials on cpu 6,
load 0.07. Geomean ratio to filcc -O2: `-O` 1.78 (instructions 2.67),
hull 1.78 (2.66), extended 1.77 (2.66). Lua tab is slower under both:
1.42, outside `-O`'s range of 1.39..1.40. lz4 -9 is faster under
extended (1.93 against 2.03). Every other workload is within its
trials' range.

**Decision.** Neither mode clears the bar for the `-O` default: a lower
geomean, and no workload slower beyond its trials' range. Both stay
opt-in, and `-O` remains `combined`.

## Not done, and why

- **First getter calls.** See [Getters](#getters-november-2026): they
  may run arbitrary code, so they still end every fact.
- **Calls that write no memory.** filcc keeps `NotFree` across calls
  LLVM proves read-only; nanofil knows nothing about callees.
- **Back edges.** Every cycle polls and a poll ends `NotFree` in filcc
  too; bounds facts from before a loop already reach it as renew
  sources. Facts first established inside a loop do not reach its
  header in either compiler's forward pass beyond what the meet keeps,
  so this was left alone.
