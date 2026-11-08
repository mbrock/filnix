# Scheduled checks: earlier traps as filcc's check scheduler makes them

Status: **prototype, opt-in** (`--checks=schedule`, November 2026). The
`-O` default stays `renew`; adopting this as the default changes
nanofil's trap contract and is the user's decision (see
[Decision needed](#decision-needed)).

nanofil's M7 work ([m7.md](m7.md)) reuses and renews check evidence
without ever moving a trap. perf.md (items 4 and 6c-2) found that the
largest remaining difference from filcc -O2 in executed checks is check
*scheduling*: filcc checks a struct pointer once, early, for every field
the code will touch, and nanofil checks each field. 6c-2 prototyped
widening within a stretch and rejected it because a trap then comes
earlier, before scalar stores that precede the failing access, and the
report names the merged access. campaign.md ("Safety and behavior
preservation are separate obligations") asks for the failure timing,
diagnostics and observable effects to be stated, the oracle extended
and the contract reviewed before adopting such motion. This document
does that.

filcc is nanofil's reference (progtest and schedule-trap.sh compare
against it), and filcc already moves traps this way. So the question is
not whether earlier traps are acceptable in Fil-C, but which precise
subset nanofil adopts, so that it is no more permissive than filcc, and
how its oracle checks it.

## What filcc's scheduleChecks permits

From `scheduleChecks` in FilPizlonator.cpp (`filc-staging-ref-src`,
around line 5915; helpers at 4352 `canonicalizePtr`, 5029
`functionWillReturn`, 5089-5110, 5770 forward AI, 3808 `emitChecks`):

**Requirements.** Each access's checks are split into kinds,
`ValidObject`, `Alignment`, `CanWrite`, `LowerBound`, `UpperBound`,
`NotFree`, `GetAuxPtr` and `EnsureAuxPtr`, each keyed by a *canonical
pointer*: a GEP base plus a constant offset. The passes are a forward
AI that removes requirements already established on every path, a
backward propagation that moves requirements to where every path will
need them, then the forward AI again.

**What moves.** Bounds, alignment, writability, valid-object and
not-free requirements. `GetAuxPtr` and `EnsureAuxPtr` never move; they
stay at their instruction (around line 6080).

**What blocks backward motion** (the loop at line 6040):

| Instruction | Effect on requirements propagated backward past it |
|---|---|
| a call not known to return (`callWillReturn`: LLVM's `willreturn`, or a named list: malloc, free, zgc_* allocation and free, zmemmove_*, zgetlower, ...) | clears all |
| a call that writes memory, or an alloca that may exit (`instructionMayFree`) | removes `NotFree` only |
| an `EnsureAuxPtr` (a pointer store) | removes `NotFree` |
| the pollcheck of a back edge | removes `NotFree` |
| a definition of the canonical pointer | removes its requirements |
| ordinary and volatile stores, loads, arithmetic | nothing |

A block ending in a back edge, return, resume, unreachable or a call
(invoke) starts with no requirements at its tail, so nothing crosses an
edge back or a function exit.

**Merges.** Backward, a block's tail requirements are the intersection
over its successors (`mergeAccessChecks(..., Backward)`), with bounds
offsets and alignments kept only where they match exactly; forward
merges take the maximum. Requirements are therefore *anticipated*:
filcc never checks on a path that would not have made the access,
except that it treats calls in its will-return list as returning.

**The trap report.** A merged check traps as one access of the merged
size: "cannot read 132 bytes when upper - ptr = 128" for a 4-byte field
at 128 merged with a 4-byte field at 0. `semantic origin` lists the
merged accesses' debug locations; `check scheduled at` names where the
check now sits. Stores between the check and the failing access do not
happen.

## nanofil's contract

An earlier trap is permitted exactly when:

1. the run would, in the reference program (every access with its own
   check, `--checks=reference`), reach an access through the same base
   object whose own check fails because those same bytes lie outside
   the object; and
2. between the scheduled check and that access the run executes only
   *transparent* instructions (`ahead_transparent/1` in ir.pl): no
   call, allocation, global getter, pointer store, atomic, setjmp,
   va_arg or division, and no poll edge, edge back or return. The
   check's own access counts: it too runs after the early trap point,
   so a check whose access is a pointer store or an atomic is never
   widened (filcc would widen it; nanofil does not).

What may then not happen are scalar stores (ordinary stores through
any pointer, including volatile ones), loads and arithmetic between the
two points. Within one process no one observes them once the program
has trapped; another thread, or a process sharing a `MAP_SHARED`
mapping, could have seen them before the process died, and with an
early trap never does. filcc -O2 drops them the same way. The
report names the merged range ("cannot read N bytes when upper - ptr =
M", as filcc's), the scheduled check's origin, and the pointer at the
check's base. The trap is still a Fil-C safety trap: the program's exit
status is the same.

Only the upper end moves (the check's lower end and alignment stay its
own access's); not-free and read-only are already the check's own, so
they cannot fail early.

This is a strict subset of filcc's permission: filcc also moves bounds
past calls in its will-return list and past calls that may free, and
merges into a check of the canonical base rather than of the first
access's pointer. nanofil stops at every call. One difference in kind:
where two successors need different extents, nanofil keeps the smaller
(both paths need at least that), where filcc's backward merge keeps
only exact matches; both are anticipated, so the earlier trap happens
only on executions that trap later anyway. Per program the two
compilers' trap text agrees where their checks merge the same accesses
(schedule-trap.sh); it is not promised in general, as filcc's merging
also depends on LLVM's inlining and GEP canonicalization.

## Checked-IR evidence

```prolog
let(tmp(Q), a, check_ahead(Lo, Hi, Rights, Align, AHi), [P])
```

is exactly `check(Lo, Hi, Rights, Align)` of P (valid_op: Lo < AHi <
Hi), of which only [Lo, AHi) is the following access's own requirement;
the bytes [AHi, Hi) are checked early. Its proof is live evidence of
[Lo, Hi) like a check's, so later accesses through P are reused or
renewed from it. This is a change to the IR grammar (ir.pl's op table).

`renew(Lo, Hi, Rights, Align)` of `[Q1, P]` now also accepts P at a
constant distance D from Q1's checked pointer P1 through one
single-definition base (`pointer_distance/4`), when Q1's check covers
[Lo + D, Hi + D) with alignment. Distance 0 is the previous rule
(`same_pointer/3`). This is what turns the later field checks into
renewals (flag tests).

## Validator rule (ir.pl, independent of the pass)

`ahead_justified/3` computes, by its own backward walk over the blocks
in reverse order, `need(B) = H`: every path from this point reaches,
before a non-transparent instruction, a poll edge, an edge to the same
or an earlier block, or the end, a raw heap access through a pointer at
an exact offset from the single-definition base B whose bytes reach B +
H, with B not redefined in between.

- A block's exit facts are the meet over its jump's edges, both arms of
  a branch counted: a plain edge to a later block carries that block's
  entry facts, any other edge none. A base present on every edge keeps
  its least H; no edge, no facts.
- Walking backward, a non-transparent instruction ends every fact, a
  definition ends its name's fact, phi destinations end theirs at the
  block's entry, and a raw access at offset Off of Size bytes, through a
  single-definition proof of P, raises need(B) to at least K + Off +
  Size for each exact base B + K of P (guard_chain/3).
- A `check_ahead` of P = B + K is accepted iff need(B) right after its
  access is at least K + Hi, its access lies in [Lo, AHi) and is
  transparent itself, and the function has no setjmp.
- Offsets from guard_chain/3 are exact only modulo 2^64 (pointer
  arithmetic wraps). A need counts only offsets K and K + Off + Size in
  [-2^62, 2^62] (`near_offset/1`), where the integer is the true signed
  distance: otherwise a + (2^63 - 4) + (2^63 - 4), which is a - 8, would
  count as needing a + 2^64. The check counts only if K + Lo is in that
  range too: otherwise its start B + K + Lo and the end of the access
  that meets the need, up to B + 2^62, could be nearly 2^64 apart, and
  wrap past each other. Bounding the need alone would not do: the meet
  keeps the least need over the edges, while the access a path runs may
  end anywhere up to 2^62.

Why that suffices: the early bytes fail only if P + Hi exceeds the
object's upper (the access's own range [Lo, AHi) passed, so the object
is live, writable if needed, aligned, and its lower end is below P +
Lo). Every path then reaches an access through B, with B's capability,
whose range ends at or past B + K + Hi, so that access's reference
check fails too. "At or past" is an integer claim about addresses
modulo 2^64: P + Lo lies in the object, below 2^48, and the access ends
H - (K + Lo) bytes after it, at most 2^63, so the sum does not wrap. Raw accesses in checked IR are the original program's
accesses; each had its own check in the reference program.

## Interpreter rule (interp.pl)

`check_ahead` runs the access test of [Lo, AHi) first and traps with
its reason if that fails: no earlier than the reference. If only [Lo,
Hi) fails, it yields P and marks the run *doomed* with the reason. A
doomed run must then reach, through transparent instructions and plain
edges only, an access whose bounds fail: a renew whose span fails, or a
raw access through the widened proof that its capability does not
allow. That outcome becomes `trap(early(Why))`. Anything else first, a
non-transparent instruction, a poll edge or a return, is
`unchecked(ahead(Why))`: a check_ahead the validator should not have
accepted.

The pizlonation oracle (`pizlonation_verdict/4` in main.pl) accepts
`trap(early(_))` iff the unchecked reference run traps (any reason). So
it accepts exactly the earlier traps the contract permits: the doom rule
ensures the failing access is reached before any effect, and the oracle
ensures the reference traps.

A renew now runs its access test on its own pointer P, which must have
Q1's capability; another object's capability is `unchecked(alias)`.

## Emitter rule (filc_amd64.pl)

`fused_blocks/5` rewrites each `check_ahead(Lo, Hi, Rights, Align, _)`
to `check(Lo, Hi, Rights, Align)` before fusion: the native check tests
the whole range, so its failure reports `Hi - Lo` bytes. Renews at a
distance emit as renews do, a flag test on P's object.

## The pass (schedule.pl)

`schedule_checks/2` runs after `renew`: it widens each heap check by
its own need analysis (`crossable/1`, a closed list that the validator's
transparent set includes), then renews at any distance
(`check_reuse:renew_checks/3`), and re-roots renews whose source check
was itself renewed. `schedule_refines/2` accepts only checks that became
a `check_ahead` with the same lower end and own range, or a renew of
the same pointer. Then `valid_module/1` decides.

## Tests and plants

- `tests/unit.pl`: `schedule_validation` (straight line, one byte over,
  diamond with both and one arm, the same edge twice, a poll edge, an
  edge back, a call, allocation, getter, division and pointer store in
  between, a scalar store in between, another base, a phi, a read of
  the proof itself, the own range, setjmp, valid_op);
  `schedule_semantics` (the doomed run, an early trap reached, an
  allocation before it, a read of the proof itself, renew at a
  distance); `schedule_pass`.
- `tests/c/prog/schedule-{early,cond,call,loop,wrap}.c` with
  `tests/schedule-trap.sh`: nanofil -O reference, nanofil -O
  --checks=schedule and filcc -O2 agree on stdout and exit status;
  schedule's first safety-error line equals filcc's; schedule-early's
  differs from the reference build's (132 bytes before the store),
  the others' equal it (no motion past a conditional arm, a call or an
  edge back).
- nix/check.nix runs difftest, ABI+GC and progtest with and without
  `-O`, and the corpus under `-O`, all with `NANOFIL_CHECKS=schedule`.

Plants, each caught, then restored: the validator's meet taken as a
union, or its transparent set including calls, or poll edges carrying
facts (schedule_validation fails); the interpreter ignoring the early
bytes, or not dooming the run (schedule_semantics fails); the emitter
checking only [Lo, AHi) (schedule-trap.sh: schedule-early then reads
past the object and prints "0 7"); the pass's meet taking one edge
(the validator refuses schedule-cond's check, so the compile fails).

## Review (November 2026)

A reviewing subagent attacked the validator, interpreter rule, oracle
and emitter. Two findings blocked adoption and are fixed:

1. **Unsound, wraparound.** The need used unreduced integer offsets, so
   an access at a - 8 reached through two adds of 2^63 - 4 counted as
   reaching a + 2^64 - 8; the meet with the other arm's a + 16 widened
   a's check to 16 bytes, which trapped natively ("cannot read 16 bytes
   when upper - ptr = 8") where filcc -O2 and the reference return 0.
   Fixed by `near_offset/1` in the validator and its own copy in the
   pass; `schedule_validation`'s wrap case and
   `tests/c/prog/schedule-wrap.c` test it (the plant removing the
   bound fails the unit test).
2. **Contract mismatch, the own access.** The validator did not require
   the check_ahead's own access to be transparent, and the pass widened
   `s->p = v; s->x = 1;`'s pointer store check over `s->x`; the
   interpreter called a run that failed early there
   `unchecked(ahead)`. Fixed on the strict side: the validator requires
   the own access to be `ahead_transparent/1` and the pass to be
   `crossable/1` (unit case; the plant removing it fails).
3. **Unsound, wraparound of the check's start** (found in November 2026
   by Campaign 3's proof, docs/rocq.md, "A need past 2^64"). The rule
   bounded K and the need H but not K + Lo. With P = a - (2^62 - 8) -
   2^62 and Lo = -2^63, P + Lo is a + 8 modulo 2^64, while K + Lo is
   about -3 * 2^62; an access ending at B + 2^62 counted as reaching
   past P + Hi but is a's byte 0, and passed. The validator accepted a
   module the interpreter ran to `unchecked(ahead(out_of_bounds))`, a
   false early trap. Fixed by `near_offset/1` of K + Lo in the
   validator and the pass; `schedule_validation` has the case (it fails
   without the bound). The pass widens the same 55 checks in tests/c
   with the bound as without it.

Found sound: conditional paths, repeated edges, irreducible flow
(block order is only conservative, since any cycle has an edge to the
same or an earlier block, which carries nothing), phis and
redefinition, same base with another capability (chains go only
through flights whose lower is the address operand), inexact offsets,
negative and positive Lo, a free in between (impossible: calls are not
transparent), renew at a distance (an unreduced D can only be refused),
the oracle (a return, poll edge or call first is `unchecked(ahead)`),
and the emitter (the rewrite precedes fusion; the 32-bit size limit
throws as for a plain check).

Open, not blocking: a doomed run turns *any* later `unchecked` into
`trap(early)` except alias and limit, so a wrongly reused proof of an
unrelated object would hide on doomed runs only. Converting only
failures of the doomed check's capability would close it.

## Measurements (November 2026)

Executed checks on the benchmark gate (nanofil/bench), by callgrind and
the check classifier of perf.md item 16 (`bench/profile/checks.py`):
full checks (each has one null test), check instructions, and the
program's own instructions. filcc's counts are its scheduled checks.

| Workload | full checks M, O → schedule (filcc) | check instructions M, O → schedule (filcc) |
|---|--:|--:|
| zlib -6 | 165.9 → 133.6 (57.8) | 1299 → 1097 (642) |
| zlib -d | 17.3 → 11.6 (2.8) | 131 → 92 (54) |
| bzip2 -9 | 381.1 → 338.1 (89.8) | 2909 → 2652 (1800) |
| bzip2 -d | 82.9 → 60.8 (42.3) | 660 → 512 (411) |
| lz4 -9 | 138.1 → 133.8 (34.2) | 1062 → 1036 (646) |
| lua int | 62.0 → 50.0 (20.0) | 484 → 392 (258) |
| lua tab | 54.1 → 46.1 (18.1) | 425 → 365 (227) |
| lua str | 74.1 → 69.5 (45.1) | 629 → 594 (410) |
| sqlite | 456.6 → 401.5 (178.4) | 3725 → 3379 (1966) |

The total number of checks run (full checks plus renewals) does not
change: the widened check's later fields become renewals, flag-only
tests. In bzip2's `copy_input_until_stop` full checks fall from 67.5M
to 49.8M and check instructions from 572M to 468M (filcc's
`handle_compress`, into which it inlines the function: 445M), while
renewals rise from 54M to 72M: the remaining difference from filcc
there is the free-flag test of each renewal, which filcc's NotFree
requirement drops where nothing between can free.

Time and instructions, `run.py --modes ref,O,O-schedule`, 5 trials on
cpu 6, which run.py found quiet before each round (geomean ratio to
filcc -O2): O 1.82 (2.80 instructions), O-schedule 1.80 (2.74). Per workload,
instructions fall 1 to 7% (zlib -d 7%, bzip2 -d 4%, lua 3 to 5%,
bzip2 -9 2.5%, sqlite 1.7%); time moves within the trials' spread
except bzip2 -9 (1.63 → 1.58) and lz4 -9 (2.03 → 1.95).

## Decision needed

1. Whether `--checks=schedule` becomes the `-O` default. It changes
   nanofil's trap contract to the one above: a trap may come before
   scalar stores and loads that precede the failing access, and names
   the merged size. The snapshot gate stays byte-identical only while
   it is opt-in.
2. Agreement to the IR grammar change: the `check_ahead` op and renew at
   a distance (AGENTS.md: the IR term grammar needs the orchestrating
   thread's agreement).
3. Whether to take the next step, which is where the remaining check
   instructions are: within a transparent stretch after a widened
   check, a later field's access could use the widened proof with no
   test at all, as filcc's NotFree requirement lets it (M7's forward
   reuse extended to accesses at a distance), and renew only across
   calls, pointer stores and poll edges. That changes no trap timing
   beyond this contract.
