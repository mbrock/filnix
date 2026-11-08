# A program logic for never_panics

November 2026. The brief for the campaign after formal.md's Campaign 7
proofs of single programs ([formal.md, Campaign 7](formal.md#campaign-7-a-program-that-never-panics)).
It records a proposal mbrock received from another Fable instance, what
the model already has that the proposal builds on, where the proposal
misreads the model, what it would cost, and a recommendation. Nothing
here is built beyond what "What exists" lists. The choice of Iris, and
whether to start at all, is mbrock's.

## The proposal in one paragraph

Campaign 3 is already a program logic, with one fixed assertion language
(the validator's facts), facts derived automatically, and adequacy proved
once ([valid_no_unchecked](../rocq/theories/Soundness.v)). never_panics
needs that assertion language opened so each program brings its own
facts, while keeping one adequacy theorem. The facts that keep a check
from failing are about the heap's shape (this field points to a live
16-byte object; this string has a NUL), and they are global, so they
should travel with ownership: separation logic, with a frame rule
carrying everything a function does not touch across a call. The logic's
weakest precondition is defined from the machine's step, with a panic
counted as stuck and a refusal, an exit or the end of fuel as final, so
that adequacy is never_panics itself. Its resources are keyed by object
identity: a persistent [meta](concepts/meta.md) fact, a
[live](concepts/live.md) token that free consumes, and points-to cells
with their aux capabilities. A check then splits into a spatial part
(arithmetic over persistent facts) and a temporal part (`live b`), and
raw accesses need no rule because Campaign 3 covers them. The runtime's
freedom to free a live heap object at a safepoint becomes a premise on
the runtime instance, not an axiom. Blocks get Floyd assertions (SSA
temporaries are logical constants), functions get specs in a table with
the frame rule and Löb induction for recursion, libc gets triples
derived from ExternalCalls.v's contracts, and each object file is proved
against its imports' specs. It recommends Iris (Cerise as prior art) and
a first spike on gc.ir's list `sum`. Above the logic sits a ladder:
validator facts, Campaign 5's certificates, RefinedC-style ownership
types, then hand proofs, each a fragment of the one below, so Campaigns
5 and 7 merge.

## What exists

| Piece | Where | Is, in the proposal's terms |
| --- | --- | --- |
| `never_panics`, `fails`, `failure_ending` | [Panics.v](../rocq/theories/Panics.v) | the safety property; `fails` already counts stuck, `UB`, `unreachable` and every non-refusal trap as one thing |
| `never_panics_by_invariant` | Panics.v | the [adequacy](concepts/adequacy.md) of the simplest logic: one global invariant of configurations, every step safe and back in it, every fresh base, and a due safepoint keeping it |
| `compute_step`, `block_fact`, `show_facts` | [Symbolic.v](../rocq/theories/Symbolic.v) | symbolic execution of one step with the environment, memory and fuel abstract; the work a wp rule per instruction would do once |
| `cycle_never_panics` | [Cycle.v](../rocq/theories/Cycle.v) | Floyd assertions at each of 19 points; a loop of any trip count |
| `buffer_never_panics` | [Buffer.v](../rocq/theories/Buffer.v) | a heap object at any fresh base; `holds_buffer` is `meta b 32 Heap` and `live b` written as one non-separating fact; `safepoint_keeps_live` is the instance premise the proposal asks for |
| `valid_no_unchecked` | [Soundness.v](../rocq/theories/Soundness.v) | Campaign 3: no run of a valid module that starts ready reaches `unchecked`; under `spares`, and stuck past any external call but free |
| ExternalCalls.v, ExternalMachine.v, Hi.v, Program.v | Campaign 4 | relational libc contracts with writable roots (a hand-rolled frame), a labelled machine, hi.c's body safety under `stdio_stable` |

So the degenerate logic and its adequacy exist, and three programs are
proved with it. What does not exist is any separation: one invariant
names everything the program holds, and a second function or a second
object means rewriting it.

## Where the proposal is right

- **One adequacy theorem, an open assertion language.** This is the
  right shape, and `never_panics_by_invariant` shows the adequacy end is
  cheap here: the machine already has the safety notion, so adequacy is
  an induction on `mreachable`. The open question is only how rich the
  assertions are.
- **Ownership keyed by identity.** Fil-C's memory is already that:
  regions by identity ([region](concepts/region.md)), bounds that change
  only at free, identities never reused in the model
  (`free_keeps_ids`), freed bytes retained
  ([retention](concepts/retention.md)), capabilities in the aux. A
  `meta` fact is persistent because nothing after allocation changes
  what was allocated, and `live` is exactly what free changes. Buffer.v
  needed precisely these two facts and nothing about bytes.
- **The spatial and temporal split.** A check's bounds part is
  arithmetic over `meta` and the pointer's offset; its flag part is
  `live`. That matches Campaign 0's census categories and lets Campaign
  5's certificates stay purely arithmetic.
- **Raw accesses need no rule.** Cycle.v and Buffer.v re-prove every raw
  load in bounds by symbolic execution, which `valid_no_unchecked`
  already guarantees for a valid module. A logic that takes Campaign 3's
  run invariant as a given only needs rules at the obligation sites and
  value rules for what a load returns. This would cut most of the
  per-program arithmetic.
- **The safepoint premise belongs to the instance.** Under Runtime.v as
  written, a safepoint may free any live heap object
  (`safepoint_lifetime`), so never_panics is false for a program that
  holds one across a poll or a call. Buffer.v states the premise as an
  antecedent, `safepoint_keeps_live`, which the interpreter meets; Hi.v's
  `stdio_stable` is the same kind of premise for stdio's objects.
- **The ladder, and Campaign 5 as a fragment.** A certificate checker
  that emits derivations in the logic is sound by adequacy, with no
  separate soundness proof against the machine.

## Where it misreads the model

- **"Raw accesses need no rule" has hypotheses.** `valid_no_unchecked`
  needs the module valid, the run started ready, and `spares`, and in
  the core machine an external call other than free is stuck, so it says
  nothing past one. For hi.c or Hello it must hold on Campaign 4's
  labelled machine (ExternalMachine.v preserves Campaign 3's invariants
  across calls, so this is near) and be combined with the logic's
  invariant: adequacy is then "the logic's state interpretation and
  Campaign 3's run invariant together are preserved", not the logic's
  alone.
- **The safepoint rely is simpler than "handlers respect ownership".**
  The model has no threads and no handlers: a safepoint is the runtime
  R acting, and what it frees stands for another thread or a handler.
  For a single-threaded program without a freeing handler, which is
  every program on the roadmap including Hello, the whole rely is
  "frees nothing live", already stated in Buffer.v. The ownership-
  respecting rely matters only for the concurrency inquiry. Its
  stability proof uses `non_moving` (bytes), `aux_round_trip` (stored
  capabilities) and `rooting` (identities), as the proposal says.
- **Shared libc state is not Iris-shaped here.** libc is not code in the
  model; it is trusted contracts over an abstract world with a `rep`
  relation to memory. The program does not touch a FILE's fields, so
  stdout is a first-order resource the program owns and lends to each
  call's contract, not a shared invariant between two pieces of code.
- **The function pointers on the roadmap have known targets.** Campaign
  4 represents the exit registry as pinned and in memory (ExitMemory.v);
  `close_stdout` and the like are a case split on `Fn f`, first-order,
  as the proposal concedes.
- **Recursion has fuel.** The machine spends one unit of fuel per block
  entry, shared by the whole stack, and `OutOfFuel` is not a failure.
  An induction on fuel therefore gives Löb's rule for recursive
  functions without step-indexing.
- **A configuration is not an expression.** Iris's `language` splits
  expression from state; a configuration holds the memory (`c_mem`), and
  the runtime's state sits beside it in `mstate`. An Iris instance needs
  a wrapper: expression the frames, callers and fuel; state the memory
  and R's state; a safepoint a step that changes only the state; a
  `Done` that is not a failure a value, and a failure stuck.
- **gc.ir's `sum` is not a closed program.** It takes the list from its
  caller and calls the external `c_gc`. never_panics over "any input"
  cannot say "the argument is a list", so the spike needs a function
  spec with a precondition, a caller (gc.ir's `build`, or a fixture
  that builds then sums), and either a contract for `c_gc` or a version
  without it.

## What it costs, measured

The proof work in Cycle.v and Buffer.v did not go into the logic. The
logic was a 25-line proof rule. It went into computing `step`, the
transcribed interpreter, on abstract states fast enough:

| Change in Symbolic.v | Effect on Buffer.v's 32 points |
| --- | --- |
| first version: `cbn` the whole step, decide wraps and comparisons with `lia`, retrying each round | 71 s |
| integer arithmetic stays folded on an unknown (`simpl nomatch`) | before this, one step did not finish |
| the function kept abstract, each block computed once (`block_fact`) | the term each rewrite traverses shrinks; `cbn` 17 s to 13 s |
| a comparison `lia` cannot decide is split at once, not retried | `decide_compares` 28% to 7% |
| a wrap `lia` cannot drop becomes an unknown in range, innermost first | 61 s to 34 s |

Neither Iris nor a hand-rolled logic removes this. What removes it is
a layer of step lemmas, one per instruction form of the core subset
(about 25: let of each op class, check and the reuse forms, flight, raw
load and store, alloc, the jumps), each proved once over an abstract
environment and memory by the same tactics, so that a program proof
never reduces `step`. In a separation logic these are the wp rules of
the instructions. This layer is the bulk of the campaign whichever host
is chosen.

Iris's own costs, concretely:

- **Dependency.** The pinned nixpkgs has `rocqPackages.iris` 4.5.0 and
  `stdpp` 1.13.0 beside Rocq 9.1.1, so it is a pin away, not a port;
  whether cache.nixos.org has them, and the CI time they add, is
  unmeasured.
- **The literate pipeline.** dterm-rocq's grammar (web/rocq, checked by
  parse.sh) does not yet read `let ... in` or `fresh` inside Ltac; Iris
  proofs are written in its proof mode (`iIntros "[Hl Hs]"`, intro
  patterns in strings) with new notation (`∗`, `-∗`, `▷`, `|==>`). The
  renderer and parse.sh would need to learn both before any Iris file is
  on the site.
- **Term size.** Iris's tactics are tuned for small expressions;
  a configuration that carries the function's body is large. The
  `block_fact` discipline would be needed there too.
- **What it buys.** Generic adequacy (here already cheap), invariants
  and ghost state (needed only for concurrency), Löb (replaceable by
  fuel), higher-order specs (not needed until a function pointer with an
  unknown target), and the proof mode, which is the real gain: framing
  and splitting separating conjunctions by hand is tedious and is where
  hand-rolled logics usually hurt.

A hand-rolled logic's costs: a heap of identity-keyed heaplets (each
`meta`, `live`, cells) with disjoint union, a small separating
conjunction with its frame lemma, the state interpretation and its
stability under alloc, free and a frees-nothing safepoint, and tactics
to frame. A first-order version of this is a few thousand lines; VST
shows how large it gets when it must also do everything Iris does.

## Recommendation

Take the proposal's architecture and change the order:

1. **Step lemmas first** (rules for each instruction over abstract
   states, from Symbolic.v's tactics). Needed whichever host; Cycle.v
   and Buffer.v are re-proved on them as the check, and should get
   faster.
2. **The resource model, first-order, hand-rolled:** heaplets keyed by
   identity with `meta`, `live` and cells; a state interpretation; its
   stability under alloc, free, and a safepoint under
   `safepoint_keeps_live`. Adequacy is `never_panics_by_invariant`
   with the state interpretation and Campaign 3's run invariant as the
   global invariant.
3. **The list-sum spike on it:** a fixture that builds a list and sums
   it (no external call), a recursive list predicate, a check per node,
   a poll on the back edge, two functions with specs and the frame rule.
   Then gc.ir's version with a `c_gc` contract on Campaign 4's machine.
4. **Decide Iris at the spike's end, on evidence:** how much of the
   spike was framing by hand, and whether Hello's census shows function
   pointers with unknown targets or other higher-order specs. In
   parallel and timeboxed, an Iris spike of the host alone: the
   `language` wrapper above, its adequacy proved equal to never_panics,
   and one small file through parse.sh and dterm-rocq, to price the
   dependency and the pipeline. If Iris wins, steps 1 and 2's content
   (step lemmas, the identity-keyed model) moves over; the hand-rolled
   separation layer is what is lost.
5. **Then the proposal's path from re-proving hi.c on:** hi.c through
   the logic with puts' triple derived from its contract, compared with
   Hi.v's direct proof; then ownership types and certificates as
   fragments; then Hello.

This leaves Buffer.v as the last single-invariant proof: the next heap
program is the spike.

## What Hello will demand

From the proposal, with what Campaign 4's contracts would need to say
for each (the contracts stay relational and trusted; a triple is
derived from each once):

| Need | Assertion | What the libc contract must state |
| --- | --- | --- |
| gnulib's string code | `string p`: identity, offset, `live`, a NUL at or after it | for each pointer argument, the bytes it reads up to a NUL; for each result, which identity it points into |
| `__ctype_b_loc` | a persistent table from −128 to 255: persistent `meta`, `live` and read-only cells | that the returned object is never freed and never written |
| `malloc`, `strdup` | `meta b n Heap`, `live b`, zeroed or copied cells | the extent of the new object; nothing else changed |
| `free` | consumes `live b` | that it frees only its argument's object |
| quotearg | a slot invariant, with the result lent: `string ret ∗ (string ret −∗ slots)` | that a buffer it returns is valid only until the next call with the same slot that grows it |
| exit, atexit | the registered functions' specs, by case on the pinned targets | the order and set of callbacks (Campaign 4's registry) |
| every call | the frame rule | the writable roots and nothing beyond them: no write, free or capability change outside the footprint |

## Open questions for mbrock

- Start the logic now, or finish Campaign 4's hi.c first?
- Iris: decide now, or at the spike's end as recommended?
- Is "frees nothing live at a safepoint" the premise wanted for every
  single-threaded program, or should Runtime.v gain a single-threaded
  runtime type that has it as an axiom with a native test?
- Should the ladder's middle rungs (types, certificates) be designed
  before the spike, or only after it shows what a derivation looks like?

See [meta](concepts/meta.md), [live](concepts/live.md) and
[adequacy](concepts/adequacy.md) for the three new terms.
