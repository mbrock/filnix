# Lowers per root: the GC-root contract of a frame

docs/perf.md item 19's lever 3. nanofil gives every pointer temporary
its own `lowers[]` entry, so a flight `&block[i]` reloads its donor's
lower and stores it again in its own entry, on every iteration. filcc
roots a derived pointer through the entry of the pointer it derives
from. Item 19 bounded this traffic at 3.4G instructions on the gate
(flights), with 1.6G more in phis. Sharing an entry changes which
entries the collector finds a live object through, so this document
states today's contract, filcc's rule, the proposed rule and the
checker that validates it. The prototype is opt-in as
`--lowers=shared` (NANOFIL_LOWERS); the default does not change, and
the snapshot shows identical outputs.

## Today's invariant

**Every pointer temporary that is live at a point of a reachable block
has its current lower in a `lowers[]` entry of its function's frame,
and only that temporary uses that entry while it is live.** The
collector marks the object of every entry in every frame on the
thread's `top_frame` chain (`filc_mark_outgoing_ptrs_in_frames`,
staging 18b6663, `filc_runtime_inlines.h:456-505`: it reads
`frame->lowers[index]` for `index < num_lowers_ish` and marks
`filc_object_for_lower`, the header just below the lower). It does this
at the thread's safepoints, so the invariant is needed at every
safepoint. nanofil keeps it at every point, which is simpler to state
and check.

Why it holds:

- **One entry per temporary for its live range.** `frame_slots.pl`
  gives each `p` temporary a pointer-pool slot, an address word and a
  lower entry allocated together, and two temporaries share a slot only
  when their closed live intervals are strictly disjoint. An interval
  covers every touch and every block boundary where the temporary is
  live, so it covers every point where it is live.
- **Every definition stores the lower.** `flight_store//2`,
  `copy_result//2`, the generic and fast call results, pointer loads,
  cas and getters write `lower(tmp(D))` when they define D; phis write
  theirs on each edge from a shadow (`phi_writes//2`). Results are
  written after the helpers they call, so an instruction never
  overwrites an entry that one of its operands still needs.
- **Zeroed at entry.** `zero_roots(N)` (`lowers_zeroing//2`) clears
  every entry before `push_frame`, so the collector never sees an
  uninitialized word.
- **A lower is never only in a register across a safepoint.** Register
  homes are scalars and, under `--registers=pointers`, address words
  (docs/perf.md 5b-2). `amd64_regs_check:valid_map/3` refuses any home
  that overlaps the frame record `[-FrameBase, -FrameBase + 16 +
  8·NLowers)` or a local object, and `placed_lines/7` passes that range
  from `layout/4`.

What relies on it:

| Code | Reliance |
|---|---|
| `filc_amd64.pl`'s frame layout (`layout/4`, `function_origin//7`) | `lowers[]` follows `parent` and `origin` at `-FrameBase`; the origin's `num_lowers_ish` is the number of roots, so the collector scans exactly the entries the function writes. |
| The register checkers | 5b-2's root-range obligation is what keeps a lower out of a register. Under 5a-loads a lower entry is a cell whose loads may be forwarded within a region; its stores stay. |
| setjmp (docs/setjmp.md) | Each temporary of a setjmp function has its own entry, never pooled. `filc_jmp_buf_recreate` copies all of `lowers[]` (`filc_runtime.c:8017-8021`) and `filc_native_zlongjmp` writes it back (`:8100-8106`), the only runtime writer of a frame's entries. An entry per name is what makes the restored lowers match the names. |
| Exceptions | A callee that raises returns with the flag set; the caller jumps to its exception exit, `pop_frame` then `exception(Return)` (`filc_abi.pl`'s `Exit`). No safepoint follows the callee's return there, and no code of the frame runs again: nanofil frames have no landing pads (origins keep `can_throw = 0`). During the raising callee the frame is as it was at the call. |
| ensure-aux | A pointer store may exit in `filc_object_ensure_aux_ptr_outline`, a safepoint; then `rooted_reload` loads the address and lower of P and V from their slots again. The liveness view keeps both live through the access (`live_inst/2`), so their entries hold them across the exit. |
| The poll slow path | `filc_pollcheck_slow` runs after an edge's phi copies (`edge_moves//4`, which also refuses a safepoint inside the copy). It may stop the thread for a handshake or a collection and run deferred signal handlers, so every temporary live at the target's entry, phis included, must be in its entry there. |

Other threads read a thread's frames only while it is not entered
(soft handshakes and stop-the-world wait for that), and nanofil code
exits only inside runtime calls, at the same points. Frame stores have
no barrier: FUGC is a grey-stack Dijkstra collector that rescans
stacks at the end of marking (docs/m3.md), and clang's code stores
frame lowers the same way.

## What filcc does

FilPizlonator's `computeLowerRoots` and `computeFrameIndexMap`
(staging 18b6663, `FilPizlonator.cpp:2914-3004` and `3006-3450`;
`-filc-share-derived-lowers`, on by default, line 69):

1. **Roots.** Each eligible value (an instruction or argument of
   pointer type whose underlying pointer is escaping, i.e. a heap
   pointer) starts as its own root. Until nothing changes, over the
   reachable blocks:
   - a GEP, bitcast or addrspacecast has the root of its pointer
     operand, if that root is eligible;
   - a phi or select has root C when every input other than itself
     has root C, C is eligible, and C dominates it: for a select, C
     dominates the select; for a phi, C is an argument or an
     instruction in another block that dominates the phi's block.
     The comment gives the reason: otherwise C may be defined in the
     phi's loop and the phi would see C's lower from the previous
     iteration.
   Unreachable blocks keep their own roots (dominance there is vacuous).
2. **No entry for derived values.** A value whose root is not itself
   gets `FrameEntryKind::Ignored` (line 3252): no frame index, and
   `recordLowersRecurse` stores nothing for it (line 3458).
3. **Roots live where derived values are used.** The liveness that
   builds the interference graph maps every operand to its root
   (`LiveCast`, line 3022), including phi inputs at the predecessor's
   tail. So a root is live wherever any value derived from it is used,
   and greedy colouring never gives its index to an interfering value.

That is the rule: *a derived pointer shares its root's entry when the
root dominates it and the root is kept live over all the derived
pointer's uses.* LLVM's SSA supplies "single definition" and
"dominance" for free. filcc does not exclude setjmp functions here;
nanofil does (below).

## nanofil's rule

**Contract (shared lowers).** At every point of every reachable block,
each live pointer temporary N's current lower is in its entry E(N).
Entries may now be shared: E(D) = E(R) when D derives from R by the
rule below. The collector's view is unchanged in kind: at a safepoint,
every live pointer's object is marked through some entry that holds its
lower, because two pointers with one lower have one object
(`filc_object_for_lower` is `lower - 1`, a header).

**Which pointers share** (`lower_roots.pl`, filcc's rule for nanofil's
two derivations):

- A flight `flight(tmp(D), Op, Args, lower(tmp(P)))` with one
  definition, whose donor P has one definition, has P's root.
- A pointer phi with one definition, all of whose inputs are
  temporaries with one definition, has root C when every input other
  than itself has root C and C is a parameter or is defined in another
  block that dominates the phi's.
- Roots are computed to a fixpoint over the reachable blocks; a name
  that is not derived is its own root. Definitions are counted on the
  liveness view, with fused accesses bare and `uses/2` unwrapped, so a
  fused pointer load cannot hide a second definition.
- Functions with setjmp share nothing.

**Why sharing is sound.** Take D derived from root R. nanofil's
validated IR is strict SSA in reachable blocks
(`ir:definitions_dominate/3`), and every name on the chain from D to R
has one definition, so R's definition dominates D's. Then whenever D is
live, the last execution of R's definition is the one D was derived
from: a path from D's definition to a use of D that ran R's definition
again would give a path from the entry to that use that avoids D's
definition (enter, reach R's definition without D's, which dominance
allows, then continue), contradicting that D's definition dominates its
use. So R's lower is D's lower whenever D is live. `frame_slots.pl`
grows R's pool interval to the hull of R's and every derived pointer's
intervals (`derived_ranges/3`), so no other temporary writes R's entry
while D is live; derived pointers get an address slot only,
`storage(address, I)`, with no lower. Hence E(R) holds D's lower
wherever D is live. For a phi, R must dominate the phi's block from
outside it; without that the loop counterexample above applies.

**What invalidates it**, each refused by the rule and caught by the
checker if a producer got it wrong:

| Hazard | Rule | Fixture |
|---|---|---|
| The root's entry reused while a derived pointer is live | the root's interval covers its derived pointers' | `dead_root` (checker), `lowers.ir` `dead_root` (native) |
| The root, or the derived pointer, defined more than once | one definition each | `redefined_root` (checker), `lowers.ir` `redefined_root` (native) |
| A phi whose root is defined after it in its loop | strict dominance from another block | `loop_phi_inner_root` |
| setjmp: longjmp restores `lowers[]` behind the analysis | no sharing in setjmp functions; the checker requires one entry per name there | `setjmp` |
| A write at a call's return while a derived pointer is live (e.g. an exception-capable call's result pooled into the root's entry) | intervals are closed, so a result never shares with a live operand | `call_result_overwrites` |
| An entry aliased to a shadow, stack-aux, snapshot or jmpbuf root | a temporary's entry is a `lower(tmp(_))` or pointer-pool entry | `shadow_entry` |

**Emission** (`filc_amd64.pl`). A flight whose donor's entry is its own
(`shared_lower/3`) loads and stores no lower. A pointer phi whose inputs
all have its entry (`shared_phi_lower/3`, only under `--lowers=shared`)
copies no lower on any edge. Nothing else changes: every other
definition still stores its lower, every check still loads the lower
from its entry, and no lower enters a register home. The flight rule
cannot fire in the default mode: a flight and its donor are both
touched at the flight, so their closed intervals overlap and they have
different entries; the snapshot confirms it.

## The checker

`lowers_check.pl` validates the frame of every function compiled under
`--lowers=shared` (a rejection is a compile error, not a fallback). It
reads only the IR, the frame's roots and aliases, and `cfg.pl`'s
liveness; it does not use `lower_roots.pl` or `frame_slots.pl`.

- **Facts:** `holds(E, Ns)`: on every path here, entry E was last
  written with a lower that is the current lower of every name in Ns.
- **Transfer:** a definition of pointer N writes `holds(E(N), [N])`
  (parameters at entry, phis on each edge, instructions in order); a
  flight whose donor P has its entry requires P in E's set and adds N;
  so does a phi whose inputs all have its entry, for the input on each
  edge. Nothing else writes a temporary's entry.
- **Merge:** per entry, the names in every reachable predecessor's
  state after the edge.
- **Check:** each live pointer is in its entry's set before each
  instruction, at the end of each block (live out and jump uses), and
  after the phis (before the first instruction).
- **Structure:** roots are distinct; each temporary's entry is a root
  of the form `lower(tmp(N))` for its own N or `lower(storage(pointer,
  _))`, never a shadow, stack-aux, snapshot or jmpbuf root; in a setjmp
  function no two names share one. A live name with no definition, or a
  shared phi with no input from a predecessor, is an error, not a
  smaller state.

The two "shares the entry of ... which does not hold its lower" errors
are defensive: the donor or input is live at that point, so the
liveness check fires first on every fixture.

What the checker trusts: that the emitter writes a pointer's entry at
each of its definitions and nowhere else, after the instruction's last
runtime call and last operand read (checked by hand at every
pointer-defining site: call results, pointer cas, alloc, getters,
va_arg, pointer loads), that it elides exactly the flights and phis the
transfer names (the emitter decides by equal frame offsets,
`shared_lower/3` and `shared_phi_lower/3`; the checker by equal root
keys; the two agree because `layout/4` gives distinct root keys
distinct entries), that cfg.pl's liveness is right (the reference frame
already relies on it), and that the runtime writes `lowers[]` only in
zlongjmp. It is a translation validator of the frame assignment, not of
the emitted assembly.

Fail-first evidence (each planted, seen to fail, restored):

- Producer, no hull extension (`derived_range/3` keeps the root's own
  interval): the checker rejects `lowers.ir`'s `dead_root` ("pointer d
  is live ... but its lowers[] entry does not hold its lower"); with
  the checker also disabled, the native run traps instead of printing
  `dead root = 111`.
- Producer, multiply-defined donors accepted: the checker rejects
  `redefined_root`; with the checker disabled the native run traps.
- Checker, calls write nothing: `other_entry` and
  `call_result_overwrites` flip. Checker, no setjmp rule: `setjmp`
  accepted. Checker, no check before instructions: `dead_root`
  accepted. Checker, any `lower(tmp(_))` accepted as a temporary's
  entry: `jmpbuf_alias` accepted. (Checker, meet as union instead of intersection: no
  fixture flips. Every live name at a join is live at the end of each
  predecessor, which is checked there, so a path that loses a name
  fails before the merge.)

## Measured

`-O --lowers=shared` (`O-lowers` in `bench/default.nix`) against `-O`,
at b23af4e3daa4 plus this change.

**Instructions** (callgrind, `profile/checks.py --categories`, the whole
gate): 57.64G → 53.96G, **−3.68G (−6.4%)**: frame stores −2.37G, frame
loads −0.81G, moves −0.52G, everything else ±0.01G. That is item 19's
3.4G bound for flights plus part of the phis. perf's user instructions
per workload, ratio to filcc: zlib `-6` 3.28 → 2.93, zlib `-d` 2.86 →
2.48, bzip2 `-9` 1.99 → 1.86, bzip2 `-d` 2.62 → 2.47, lz4 `-9` 2.54 →
2.42, Lua int 1.68 → 1.42, Lua tab 1.58 → 1.36, Lua str 1.48 → 1.43,
SQLite 1.81 → 1.72; gate geomean **2.67 → 2.47**.

**Time.** The 7-trial run was on a loaded swa (load 50–70, other
threads' builds), so its times are indicative only: geomean 1.75 → 1.67
of filcc, with zlib `-6` 2.38 → 1.98, Lua int 1.17 → 1.03, and two
regressions. Rerun at 15 trials on the same machine:

| Workload | time ratio to filcc, O → O-lowers | cycles | instructions |
|---|--:|--:|--:|
| SQLite | 1.76 → 1.77 | 5.26G → 5.33G (+1.3%) | 20.19G → 19.17G (−5.1%) |
| bzip2 `-d` | 2.23 → 2.30 | 0.99G → 1.04G (+5.2%) | 3.75G → 3.53G (−5.8%) |

So fewer instructions do not reach time everywhere. In bzip2 `-d`'s
`BZ2_decompress` moves rise by 55M while frame stores fall by 165M: the
changed slot pooling changes temps' second lowering (the frame-layout
note in perf.md 5b-2), the same layout sensitivity bzip2 `-d` showed
before. SQLite also takes 8% more branch misses. Both need a
quiet-machine measurement before a default.

**Frame sizes** (sum of nanofil functions' `sub $N, %rsp`): zlib −1.5%,
bzip2 −1.9%, lz4 −0.7%, Lua +0.1%, SQLite +0.1% (767 functions smaller,
956 larger: a root kept longer can stop two pointer slots from pooling).

**Compile time:** c-testsuite 00200, 3.1 s → 3.4 s; `bigfn` 300, 2.8 s
→ 2.5 s (noise on a loaded machine).

**Validation**, all under `--lowers=shared`, GC stress
(`FUGC_SCRIBBLE=1 FUGC_VERIFY=1`) wherever a program runs: run-c's
interop, gc, variadic, float, setjmp, pointer-effects, lower-donor,
exceptions, reuse-gc, asm-fixed and lowers, with and without `-O` and
under `--registers=temps`; `trace-pointer-effects.sh` (20 actual
ensure-aux exits) with and without `-O`; all 203 progtests with and
without `-O`; difftest of fixtures, backend, filc IR, `tests/c` and a
300-function `bigfn` under `-O`; the cproc and c-testsuite corpus under
`-O` (262 pass, no checker rejection); the eleven gate workloads
produce filcc's output. The Nix check runs these. Default output is
unchanged (`tests/snapshot.sh`).

## Review

A reviewing subagent attacked the contract from the collector's side
(concurrent marking and handshakes, phi parallel copies, loops and the
dominance lemma, unreachable blocks, parameter, variadic, tuple, getter,
cas and va_arg roots, fused and `uses/2` definitions, ensure-aux exits,
setjmp, exceptions, the checker's trust base), with its own GC-stress
programs (array walks, interior pointers, two allocating threads) and
plants. **No blockers.** With the producer's hull extension removed and
the checker disabled, its programs trapped; with the checker on, the
same plant was a compile error. Its findings, now addressed:

1. The emitter and checker decide elisions separately (offsets vs.
   keys): stated in the trust list above.
2. The checker accepted a temporary aliased to a jmpbuf root
   (`lower(tmp(hidden(setjmp_buf(_))))`); unreachable today (setjmp
   functions share nothing), now refused, fixture `jmpbuf_alias`.
3. Writes treated as at the end of an instruction: now in the trust
   list, with the sites checked.
4. Two fail-open spots on malformed input (a live name without a
   definition; a shared phi without an input from a predecessor): now
   errors.
5. The "does not hold" errors are defensive: stated above.
6. A shared phi leaves its shadow's lower entry stale longer: objects
   may live longer, never shorter (FUGC does not move objects).

## Decision needed

Making `--lowers=shared` the `-O` default changes the GC-root contract
from "one entry per pointer temporary" to the contract above. It is the
user's decision.
