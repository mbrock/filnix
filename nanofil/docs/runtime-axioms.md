# The runtime as axioms

Campaign 2 of [formal.md](formal.md): one page of facts about the Fil-C
runtime that the Rocq model takes as given, stated at the runtime's
interface, each with a native test that would fail if the fact were
stated in the obvious stronger way the runtime does not promise. In
Rocq the page is `Module Type Runtime` in
[Runtime.v](../rocq/theories/Runtime.v), line for line with the table
below; [rocq.md](rocq.md) describes the rest of the model.

Read against the staging Fil-C the toolchain pins: mbrock/fil-c at
[`18b6663a2785`](https://github.com/mbrock/fil-c/commit/18b6663a2785c8eba6cc2a544a7711e19fc448c7),
the `coreRev` of `lib/filc-staging.json`. Revisit whenever Filnix bumps
it. Build the reference tree with
`nix build -o /tmp/filc-ref .#lib.x86_64-linux.filc-staging-ref-src`;
the runtime paths below are relative to `libpas/src/libpas/` there.

## The axioms

| Axiom | Statement | Native test | Source |
| --- | --- | --- | --- |
| `fresh_allocation` | an allocation the runtime makes has a `fresh` base: no identity the memory has, live or freed, aligned, overlapping no object, ending at or below 2^64, reading as zero with no stored capability; for a runtime state `ready` for the memory | [axiom-fresh.c](../tests/c/prog/axiom-fresh.c): new objects read zero; a freed object's capability, still held, traps after collections and thousands of allocations of its size | `filc_runtime.c` `finish_allocate_small`/`_large` (zero mode), `fugc.h:170–181` |
| `address_space` | where the runtime is `ready`, every object lies in [0, 2^48] (`objects_fit`), so no address inside one wraps, two addresses of one object are less than 2^63 apart, and an address that wrapped below 0, read signed, is below every object; the runtime's `alloc` may refuse, and the run then traps `out_of_memory` | [axiom-address.c](../tests/c/prog/axiom-address.c): heap objects of 1 byte to 1 GiB, static and initialized data and an address-taken local end below 2^48; `malloc(2^48)` traps as too big, and `malloc(2^48 - 1)`, within the size limit, traps out of memory | `filc_runtime.h` `filc_prepare_allocate_object` (`FILC_MAX_ALLOCATION_SIZE`, `PAS_MAX_ADDRESS`), `FILC_OBJECT_AUX_PTR_MASK` (object addresses stored in 48 bits), `pas_config.h` `PAS_ADDRESS_BITS` 48 |
| `non_moving` | at a safepoint no byte moves or changes: the collector writes no object's contents and no address word | [axiom-nonmoving.c](../tests/c/prog/axiom-nonmoving.c): addresses of live and freed objects, and live contents, unchanged across six collections | Manifesto.md, "Non-moving" |
| `free_lifetime`, `safepoint_lifetime` | an object's bounds change only by free, which empties a live heap object's for every alias at once; nothing else changes a region, and no identity appears | [axiom-lifetime.c](../tests/c/prog/axiom-lifetime.c): a read after a free through an alias traps; another object is untouched | `filc_runtime.c:3160–3183` (`free_impl`: `upper = lower`, then FREE), `3869–3917` |
| `safepoints` | the runtime acts (a signal handler, a pollcheck callback) only at instructions that are not `evidence_preserving/1`: calls, polls, alloc and the rest; this is one thread's view, and another thread's frees show elsewhere (below) | [axiom-safepoint.c](../tests/c/prog/axiom-safepoint.c): a timer's handler frees the object a loop reads; the loop reads only its bytes, then traps. [axiom-threads.c](../tests/c/prog/axiom-threads.c) records the limit: another thread's free traps a check after an earlier check of the same object passed, with no safepoint between | Manifesto.md, "FUGC relies on safepoints"; `filc_runtime.c:1191` (`handle_deferred_signals`) |
| `retention` | free changes no byte and no stored capability: a freed object's memory is retained while anything can name it | [axiom-retention.c](../tests/c/prog/axiom-retention.c): another thread frees the object a loop reads and churns the allocator; the loop reads retained bytes or traps, never other values | `free_impl` writes only the header; Manifesto.md on freed objects |
| `aux_round_trip` | at a safepoint a stored capability stays, or, if its object was freed, becomes one that traps as a freed object does (the free singleton) | [axiom-aux.c](../tests/c/prog/axiom-aux.c): a stored pointer to a freed object loads back at its address and traps; a live one reads | `fugc.h:170–181, 220–231` (CAS of the lower to `filc_free_singleton`) |
| `free_keeps_ids` | free reclaims nothing: every identity before a free is one after it, the freed object's too; only the collector reclaims, at a safepoint | [axiom-identity.c](../tests/c/prog/axiom-identity.c): its capability traps, before and after a collection (refuting "free leaves every region as it was"); 1024 allocations of its size right after the free, just after a full collection and while no other runs (checked with `zgc_requested_cycle`, retried up to five times; about 80 KiB with headers, below `fugc_minimum_threshold`), never take its address; another object is untouched | `filc_runtime.c:3160–3183` (`free_impl` writes only the header), `3897–3923` (`free` reaches it directly), `fugc.c:64` |
| `free_checked` | free frees or traps; it never goes on having done something else, so it gives no `unchecked` | [axiom-free.c](../tests/c/prog/axiom-free.c): free of null and of a live object's base return, the object then traps; a second free, before or after a collection, an interior pointer and a global's address trap | `filc_runtime.c:3897–3923` (`FILC_CHECK` and `free_fail` panic) |
| `rooting` | at a safepoint no identity the program can name is reclaimed | [axiom-rooting.c](../tests/c/prog/axiom-rooting.c): objects held only by a frame, and one only through another object, survive collections and allocation; with `FUGC_SCRIBBLE=1` in the gc-stress steps; [gcglobals.c](../tests/c/prog/gcglobals.c) for globals | Manifesto.md, "Accurate" |

The tests are ordinary `tests/c/prog` programs: progtest.sh builds each
with nanofil and with filcc and compares them, and its `.expected` file
holds the answers derived from the axiom, all "yes". A trap is observed
in a forked child with its stderr closed, so each program exits 0.

## How the model uses them

The model is one thread's. A free by one of its signal handlers, which
Fil-C runs only at pollchecks and exits to the runtime, and the
collector's rewriting of a stored capability are what the program finds
changed at a safepoint, the module type's `safepoint` relation, and
nowhere else.

Another thread is outside the model. Its writes already are:
`non_moving` lets no byte change at a safepoint. So are its frees,
which natively show at any check, not only at a safepoint:
[axiom-threads.c](../tests/c/prog/axiom-threads.c) has one thread check
`obj[0]`, run straight-line arithmetic with no call or pollcheck, and
check `obj[1]` while another thread frees `obj`; the second check traps
after the first passed, which no run of the model can do. A valid module
can make such a free observable without a trap, too: a `span_test` after
a check that passed may answer 0.

For a threaded program, native safety therefore rests on Fil-C's own
argument, not on the theorems proved over this module type. Every
native check traps on a freed object: renew, `renew_if` whose guard
passed, `check_limit` and the lower half check test the free flag;
check, `check_ahead` and the upper half check test the bounds; a
`span_test` that answers 0 sends `renew_if` to the full check. An access
whose check passed before the free reads the object's retained bytes
(`retention`), and a free only empties bounds, never moves them. Covering
threads in the model would need a free the runtime may make before any
instruction, run theorems weakened to "checked, or its object was freed
since its check", and a story for data races.

A freed object's address can become a new object's natively once
nothing names the old one. The model's `fresh` never reuses an
identity, because nothing dies in the model: the two agree on whether
each access through a capability a program still holds traps, though
not on its address bits after a collection. This is why the fresh test keeps the
old pointer alive, and why it does not ask that addresses never recur.

Writing axiom-identity.c showed why its claim stops at the first
collection. After one, a freed object's address may be reused even
while a local holds the pointer: nanofil keeps every C local in a
memory slot, and the collector redirects a stored capability to a freed
object to the free singleton and reclaims the object, while clang keeps
the same local in a frame root, which the collector marks without
looking at the FREE flag. Either way the old capability traps.

The model and native agree on how every capability a program holds
behaves, whether it reads or traps, not on its address bits. With
`free_keeps_ids`, `rooting` and `fresh_allocation` the model never gives
a freed object's base to a later allocation; natively a stale pointer's
address may equal a new object's after a collection, though the
pointer itself traps. The previous axioms already implied this.

`free_keeps_ids` is about `free`, the only external call the model
sends to the runtime's free (`external_call` in Semantics.v). Native
`munmap` and `shmdt` free and then unmap at once, so their range can
return from a later `mmap` with no collection; routing them through
`free` would make the axiom false.

Writing axiom-free.c found a disagreement the axioms do not cover:
native free of an escaping local's address returns, under both nanofil
and filcc (the local is an ordinary collected object natively), while
the model's free (`object_free_res` in Memory.v) traps `invalid_free`
for every object that is not a heap object. `free_lifetime`'s
`lifetime_step` lets a free empty only a heap object, so no runtime of
the module type can match native there. The test leaves that case out;
it is a fidelity question for `free_res` and `free_lifetime`, not a
safety one, and a follow-up.

## The interpreter's instance

`InterpRuntime` in Runtime.v is interp.pl's runtime: `alloc` is
`alloc_base/6` with Next from 2^32 up to 2^48, refusing an allocation
that would pass 2^48 (`address_space/2`), `free` is `free_res/4`,
`at_safepoint` is the negation of `evidence_preserving/1`, and nothing
changes at a safepoint. It proves every axiom, so the module type is
consistent and `Print Assumptions` of the extracted `judge` is closed.
Its `ready` says every object lies between 0 and Next, empty if freed,
Next is at most 2^48, and nothing at or above Next has been written. Run.v's `Driver` runs over any `Runtime`, and the
gates run `Driver InterpRuntime`.

## Readiness

Three more obligations of the module type are about the runtime's own
bookkeeping rather than Fil-C, so they have no native test.
`freed_bounds`: no freed object of a memory the runtime is ready in has
bounds (`freed_empty`). Every free and the end of every invocation
already empty them (`lifetime_step`, `region_step`), so it constrains
only the memory a run starts in. `ready_kept`: the program's writes
inside objects and its ending of objects leave the runtime ready to
allocate. `safepoint_ready`: the runtime's actions at a safepoint do
too. With `fresh_allocation` the last two make `ready` an invariant of
every run: Machine.v's `mreachable_ready` proves it for every runtime,
and `InterpRuntime` proves all three.

## The address space

The model's addresses wrap modulo 2^64 (`raw_address/3`) while its
bounds are unbounded integers, so an object ending past 2^64 would let a
covered access wrap outside it: Coverage.v's lemma needs `objects_fit`.
Before `address_space`, the interpreter's allocator only added, and
`rocq/tests/huge-object.ir` placed an object 64 bytes below 2^64 and ran
a valid module unchecked ([rocq.md](rocq.md), "An object past 2^64").

Fil-C refuses such objects in two ways, both safety errors. A size over
`FILC_MAX_ALLOCATION_SIZE` (2^48 - 1) traps before anything is
allocated, "attempt to allocate object that is too big"; that is part of
the `alloc` op itself, the same for every runtime (`alloc_res/6`,
`trap(too_big)`). A size within the limit that the address space cannot
hold traps "out of memory"; when that happens depends on the machine, so
it is the runtime's choice: `alloc` returns `None`, and the run ends
`trap(out_of_memory)`, whether the object was a heap object, a named
local or a variadic callee's argument snapshot. (Natively the snapshot
is a heap object but a named local is a stack frame slot, so only the
model refuses a local.) The interpreter's address space ends at 2^48,
libpas's (`PAS_ADDRESS_BITS`); natively memory ends sooner, so sizes the
interpreter allocates may trap natively, which the axiom allows.
`tests/filc/alloc-limit.ir` checks that both trap natively too, and
axiom-address.c checks each one's message, which pins the size limit.

The bound is native's, 2^48, not merely 2^64 (mbrock's decision). One
check's covered access needs only that no object end past 2^64, but
`hull_covered/7` joins spans of several checks of one object, each at a
near offset (within 2^62) of the access, modulo 2^64. With an object
larger than about 2^63 two such spans can sit on either side of the
wrap and the access between them outside the object
([rocq.md](rocq.md), "Objects end below 2^48"). The same bound supplies
`half_known/6`'s and `hull_renewable/8`'s assumption that a checked
address is a user address below 2^56. axiom-address.c tests that heap
objects, static and initialized data and an address-taken local end
below 2^48, and the interpreter's instance keeps Next at most 2^48.

A lower half check (`half_bound/6`) reads its address signed and fails
on any freed object, where the whole check fails only on an address
outside the object's bounds. The two agree because objects start at or
above 0, which native addresses, being unsigned, always do, and because
a freed object's bounds are empty (`freed_bounds`). Free and the end of
an invocation always empty them (`lifetime_step`, `region_step`); the
obligation says no memory the runtime is ready in holds a freed object
with bounds, natively because `free_impl` sets `upper = lower` before it
marks the object FREE ([rocq.md](rocq.md), "Renew and the half check").

The axioms speak of states the runtime is ready in. Whether a valid
module's initial memory is one is open: its data has no size limit
([rocq.md](rocq.md), "An object past 2^64").

## What is not yet stated

- Other threads' ordinary writes to shared objects are not modeled;
  they belong to Campaign 4's environment contracts.
- The fresh test cannot observe that a capability is a new identity
  rather than a reused one; it observes only that the old one still
  traps.
