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
   (`tests/c/prog/hull-far.c`, in progtest).
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

## Not done, and why

- **Getters.** A getter is a call into the global's getter, which may
  initialize it and exit, so it ends live facts. copy_input_until_stop's
  `BZ2_crc32Table` getter in its loop body is the largest remaining
  case seen. Keeping facts across getters needs a stated rule for what
  a getter may do (decision below).
- **Calls that write no memory.** filcc keeps `NotFree` across calls
  LLVM proves read-only; nanofil knows nothing about callees.
- **Hull renewals.** A full check that the hull of several dominating
  checks covers could become a flag test (item 16's 45M "full checks
  that could become renewals" are partly this), but a renew names one
  source. That needs a renew with several sources, an IR grammar change.
- **Back edges.** Every cycle polls and a poll ends `NotFree` in filcc
  too; bounds facts from before a loop already reach it as renew
  sources. Facts first established inside a loop do not reach its
  header in either compiler's forward pass beyond what the meet keeps,
  so this was left alone.
