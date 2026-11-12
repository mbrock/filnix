# A program logic for never_panics

The libc-contract examples on this page are retained reference proofs.
Their string and output triples now live in
[LibcStringLogic.v](../rocq/theories/hello_contracts/LibcStringLogic.v), and their
allocation, copying, and search triples live in
[LibcMemLogic.v](../rocq/theories/hello_contracts/LibcMemLogic.v).

[StringLogic.v](../rocq/theories/logic/StringLogic.v) and
[MemLogic.v](../rocq/theories/logic/MemLogic.v) keep the shared ownership
assertions and instruction rules used by the live glibc campaign.

The historical line counts and timings below describe the modules before
this split, when those assertions and libc triples were in the same files.

November 2026. The brief for the campaign after formal.md's Campaign 7
proofs of single programs ([formal.md, Campaign 7](formal.md#campaign-7-a-program-that-never-panics)).
It records a proposal mbrock received from another Fable instance, what
the model already has that the proposal builds on, where the proposal
misreads the model, what it would cost, and a recommendation. Beyond what
"What exists" lists, only the two list-sum spikes are built, off the
main path. The choice of Iris, and whether to start at all, is
mbrock's. [iris.md](iris.md) explains Iris itself, its history and
model, and reads the Iris spike.

## The proposal in one paragraph

Campaign 3 is already a program logic, with one fixed assertion language
(the validator's facts), facts derived automatically, and adequacy proved
once ([valid_no_unchecked](../rocq/theories/soundness/Soundness.v)). never_panics
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
| `never_panics`, `fails`, `failure_ending` | [Panics.v](../rocq/theories/logic/Panics.v) | the safety property; `fails` already counts stuck, `UB`, `unreachable` and every non-refusal trap as one thing |
| `never_panics_by_invariant` | Panics.v | the [adequacy](concepts/adequacy.md) of the simplest logic: one global invariant of configurations, every step safe and back in it, every fresh base, and a due safepoint keeping it |
| `compute_step`, `block_fact`, `show_facts` | [Symbolic.v](../rocq/theories/logic/Symbolic.v) | symbolic execution of one step with the environment, memory and fuel abstract; the work a wp rule per instruction would do once |
| `cycle_never_panics` | [Cycle.v](../rocq/theories/programs/Cycle.v) | Floyd assertions at each of 19 points; a loop of any trip count |
| `buffer_never_panics` | [Buffer.v](../rocq/theories/programs/Buffer.v) | a heap object at any fresh base; `holds_buffer` is `meta b 32 Heap` and `live b` written as one non-separating fact; it once took `safepoint_keeps_live`, the instance premise the proposal asks for, which Runtime.v's `collector_live` now makes a lemma |
| `valid_no_unchecked` | [Soundness.v](../rocq/theories/soundness/Soundness.v) | Campaign 3: no run of a valid module that starts ready reaches `unchecked`, over every runtime; stuck past any external call but free |
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
  first written, a safepoint could free any live heap object
  (`safepoint_lifetime`), so never_panics was false for a program that
  holds one across a poll or a call. Buffer.v stated the premise as an
  antecedent, `safepoint_keeps_live`, which the interpreter meets; Hi.v's
  `stdio_stable` is the same kind of premise for stdio's objects. The
  safepoint axiom is now the collector's alone, `collector_live` (no
  region changes at a safepoint), which makes `safepoint_keeps_live` a
  lemma for every runtime, so the premise is gone.
- **The ladder, and Campaign 5 as a fragment.** A certificate checker
  that emits derivations in the logic is sound by adequacy, with no
  separate soundness proof against the machine.

## Where it misreads the model

- **"Raw accesses need no rule" has hypotheses.** `valid_no_unchecked`
  needs the module valid and the run started ready (it no longer takes
  `spares`, which every runtime meets, by `spares_any`), and in
  the core machine an external call other than free is stuck, so it says
  nothing past one. For hi.c or Hello it must hold on Campaign 4's
  labelled machine (ExternalMachine.v preserves Campaign 3's invariants
  across calls, so this is near) and be combined with the logic's
  invariant: adequacy is then "the logic's state interpretation and
  Campaign 3's run invariant together are preserved", not the logic's
  alone.
- **The safepoint rely is simpler than "handlers respect ownership".**
  The model has no threads and no handlers: a safepoint is the runtime
  R's collector acting, and Runtime.v's `collector_live` says it
  changes no region, so no program states a rely at all. A signal
  handler or another thread is program code. In the model installing a
  handler (`signal`, `sigaction`) or starting a thread
  (`pthread_create`) is a call to an external with no contract, which
  ends the run as a failure, and the run is the program's whole
  execution after the trusted entry, with no handler installed and no
  other thread when it starts. That covers Hello, which installs no
  handler. The ownership-respecting rely returns when a
  handler is verified as program code, with an invariant that it frees
  only what it was handed, and in the concurrency inquiry. Its
  stability proof uses `non_moving` (bytes), `aux_round_trip` (stored
  capabilities) and `collector_live` (regions and identities, with
  `rooting` now a lemma from it), as the proposal says.
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
  functions without step-indexing; but not for a safepoint, which
  spends none (see the spikes below).
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
  cache.nixos.org has both (measured in the spikes below).
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

## The list-sum spikes

mbrock asked for the spike overnight, both ways. Both are in
`rocq/spikes`, off the main build: nothing in
rocq/theories imports them, the quick gate and CI do not build them,
and only their own check, `nix build .#checks.x86_64-linux.nanofil-logic-spikes`
([spikes.nix](../nix/spikes.nix)), depends on Iris. Both prove the same
statement about the same program, in Panics.v's terms:

```
Theorem listsum_never_panics :
  P.never_panics ls_module (TAtom "listsum") (fun xs => exists n rest, xs = WInt n :: rest).
```

The program is [listsum.c](../rocq/spikes/listsum.c), closed, so the
core machine runs all of it: `listsum(n)` allocates n 16-byte nodes on
the collected heap, links each with a checked pointer store, and calls
`sum`, which walks the list with a check of each value, a lower half
check and an aux pointer load for each next pointer, and a poll on the
back edge. gc.ir's `sum` is the same loop with an external `c_gc` call
in it, which needs Campaign 4's machine. `keeps_live` (no safepoint
frees a live object), once Buffer.v's premise and the spikes', is now a
lemma of Pieces.v from Runtime.v's `collector_live` (a safepoint
changes no region), so the theorem holds for every runtime; `Print
Assumptions` of the interpreter's corollary is closed for both.

They share [Pieces.v](../rocq/theories/logic/Pieces.v), the resource model:
pieces keyed by [identity](concepts/identity.md) (an object's life,
one byte, one aux slot at an offset), the global fact that live objects
are disjoint, and `safepoint_shape`: a safepoint keeps every region
and every byte, and rewrites only aux slots that hold a freed object's
capability (from `collector_live`, `non_moving` and
`aux_round_trip`). Keying by identity is forced, not
chosen: the model's `fresh` lets a new object take a freed one's
addresses.

| | Hand-rolled ([Sep.v](https://github.com/mbrock/filnix/blob/a8083f593eeb47a6e1e919a84f53bbe718e8594f/nanofil/rocq/spikes/Sep.v), [SepListSum.v](https://github.com/mbrock/filnix/blob/a8083f593eeb47a6e1e919a84f53bbe718e8594f/nanofil/rocq/spikes/SepListSum.v)) | Iris 4.5 ([IrisLang.v](https://github.com/mbrock/filnix/blob/177d06baaf08b8d144af534c4c73ca7bcdffcf37/nanofil/rocq/spikes/IrisLang.v), [IrisHeap.v](https://github.com/mbrock/filnix/blob/177d06baaf08b8d144af534c4c73ca7bcdffcf37/nanofil/rocq/spikes/IrisHeap.v), [IrisListSum.v](https://github.com/mbrock/filnix/blob/177d06baaf08b8d144af534c4c73ca7bcdffcf37/nanofil/rocq/spikes/IrisListSum.v)) |
| --- | --- | --- |
| Assertions | `fp -> mem -> Prop`, a footprint of pieces and the memory; `star` splits the footprint | `iProp` over `gen_heap piece pval`; the state interpretation ties the ghost heap to `mem` |
| [Adequacy](concepts/adequacy.md) | none new: `never_panics_by_invariant`, with an invariant of configurations built from the assertions | 174 lines, 2 s: the machine as an Iris `language` and `wp_never_panics`; done in an hour, no dead end |
| Generic logic | 932 lines, 3 s: star algebra, stability, footprint lemmas for each store, allocation, a frame-generic list | 786 lines, 7 s: one lifting lemma and rules for next, done, a byte or aux write, allocation |
| The program | 626 lines, 29 s | 488 lines, 59 s |
| `sum`'s spec | a step lemma for any callers and any frame F: `lst p xs ** F` to `htrue ** F` | `lst p xs -∗ (∀ y, caller's wp) -∗ wp(sum)`, for any caller and callers; the frame rides in the wand |
| The list predicate | a `Fixpoint` into `hprop`; unfolding, dropping walked nodes and reassociating stars by hand (`lst_cons_drop`) | a `Fixpoint` into `iProp`; `iDestruct` does the work |
| The back-edge poll | one lemma per function (`sum_safepoint`, `ls_safepoint`): every assertion is `sp_stable`; never looks where a safepoint is due | once, in `wpc_lift`, by Löb (about 30 lines); no program proof mentions safepoints |
| Loops | invariants at points, as Cycle.v | Löb on the loop head |
| Planted bugs | a list that does not own `live b`: the value check of `sum` cannot be proved; `lst` without an alignment fact: false, and the proof found it | a node without its `live` piece: `lst_head` cannot show the next node is live, only registered, so its checks cannot pass |
| dterm-rocq (parse.sh) | Pieces.v reads; Sep.v 40 of 114 items and SepListSum.v 24 of 55 do not, nearly all for the one infix `**` and its `%h` scope | IrisLang.v 3 of 14, IrisHeap.v 35 of 62, IrisListSum.v 29 of 47 do not: Unicode connectives (`∗ -∗ ▷ ⊢ |={⊤}=>`), `WP … {{ }}`, `Canonical Structure`, proof-mode strings, ssreflect `rewrite {2}/x` |

What each spike taught:

- **The step is still the cost.** In both, most of the program proof's
  compile time is computing `step` on an abstract state, as in
  Cycle.v and Buffer.v. Iris made it worse, not by itself but because
  `wpc_next` leaves the next configuration as an existential variable
  that the computed step must unify with: Symbolic.v's `drop_wraps` and
  `decide_compares`, which generalise or split, break that unification,
  so the Iris side wrote non-splitting copies, and the one undecidable
  comparison is split by hand. The step lemmas of the recommendation
  below remove this in both and would bring IrisListSum.v under the
  35 s line.
- **Framing by hand is where the hand-rolled logic hurts,** as
  expected: footprints are predicates, so `emp ** P` is `P` only up to
  "the same pieces" (no extensionality), and the proofs were arranged
  never to eliminate `emp`; reassociating four-way stars for a node took
  explicit lemma chains. Iris's proof mode makes all of this vanish.
- **Safepoints are where Iris clearly wins.** A safepoint step leaves
  the expression as it was and changes the state; in Iris that is one
  Löb induction in the lifting lemma, and every later proof is silent
  about polls. The hand-rolled logic needs each function's assertions
  to be `sp_stable` and a lemma per function to say so. Cheap (0.5 s
  each, mechanical) but per program. Fuel does not help here, as this
  document claimed above: a safepoint spends no fuel.
- **Calls need a design either way.** The Iris language keeps the
  callers stack inside the expression, so there are no evaluation
  contexts and no `wp_bind`; the spike's call rule passes the caller's
  continuation as a wand. That frames for free but returns nothing to
  the caller, so a spec that hands the list back needs list segments or
  an `ectx_language` with the callers as the context. The hand-rolled
  spike's frame-generic step lemma is the same idea, first-order.
- **Friction with Iris is real but bounded.** Importing it swaps in
  ssreflect's `rewrite` (no `by` clause), `++` and `+` change scope,
  gen_heap's `↦` is local to its file, and Ltac cannot name a hypothesis
  that an intro-pattern string introduces. Each was found once.
- **Both logics found something.** The hand-rolled list predicate
  first lacked a node's 8-byte alignment, which `sum`'s half check
  and pointer load test; without it `lst p xs ** F` admits lists on
  which `sum` traps.
- **Iris is cheap to have.** `rocqPackages.iris` 4.5.0 and `stdpp`
  1.13.0 come from cache.nixos.org for the pinned Rocq 9.1.1; loading
  Iris and the compiled model together takes 2.5 s.

## Recommendation

Iris, decided on this evidence rather than at a later spike's end as
first recommended here. The two spikes are the same size (about 1,550
lines each) and prove the same thing; what separates them is where the
next proofs will spend effort. Iris's adequacy into `never_panics` cost
174 lines; its proof mode removes the framing that dominated the
hand-rolled generic layer; safepoints are handled once; and Hello's
hardest case, quotearg's lent-out buffer (`string ret ∗ (string ret −∗
slots)`, below), is a wand, which a first-order logic would have to
encode. The costs to pay first:

1. **Step lemmas,** one per instruction form of the core subset, over
   abstract states, as the rules of the Iris wp. Needed whichever
   host; they cut both spikes' compile time and remove the existential
   variable problem. Re-prove Cycle.v and Buffer.v on them as the check.
2. **An `ectx_language`** whose context is the callers stack, so calls
   are `wp_bind` and a function spec returns its resources to the
   caller; then `sum`'s spec as a Hoare triple.
3. **dterm-rocq learns Iris:** the connectives above as notations,
   `WP … {{ }}`, and the proof mode's string patterns. parse.sh shows
   exactly which items fail; the spike files are the test corpus.
4. **Iris in the main build** once the above works, with spikes/
   becoming the campaign's first theories. Persistent `meta` as
   `ghost_map` elements (`↪□`), which the spike did not need because
   bounds came from the `live` token.
5. **Then the proposal's path:** hi.c through the logic with puts'
   triple derived from its contract, compared with Hi.v; gc.ir's `sum`
   with a `c_gc` contract on Campaign 4's machine; certificates and
   ownership types as fragments; Hello.

The hand-rolled spike was the record of the alternative and of what
the logic must prove about Fil-C's memory, which Pieces.v holds for
both. It and the Iris spike were removed from the tree in November
2026; the links in the table above go to their last versions, and
ListSumLogic.v proves the same program in the program logic. Buffer.v remains the last
single-invariant proof; BufferLogic.v proves the same theorem through
the program logic.

## Progress

mbrock chose Iris (November 2026), in the Iris, RustBelt and Cerise
tradition. Steps 1 to 4 above are done, and step 5 is under way:

| Step | Where | Result |
| --- | --- | --- |
| 1, step lemmas | [StepRules.v](../rocq/theories/logic/StepRules.v), on the main build | one forward rule per instruction form and jump; Cycle.v 13 s to 4.4 s and Buffer.v 23 s to 7.4 s through Symbolic.v's `take_step` |
| 2, the language | [Language.v](../rocq/theories/logic/Language.v) | an `ectxi_language` whose context is the callers stack; fuel in the state; a return to a caller is two Iris steps; endings that are neither failures nor returns stall; `wp_never_panics` proves Panics.v's `never_panics` |
| 2, the rules | [Logic.v](../rocq/theories/logic/Logic.v), [Heap.v](../rocq/theories/logic/Heap.v) | the identity-keyed ghost heap (Heap.v) and its state interpretation; one lifting lemma closes safepoints and stalls by Löb; a weakest-precondition rule per instruction (`wp_check`, `wp_raw_load_pointer`, `wp_alloc`, `wp_call_bind`, ...) |
| 2, the list sum | [ListSumLogic.v](../rocq/spikes/ListSumLogic.v) | `sum`'s triple `{{{ lst p xs }}} sum {{{ RET Ret (list_sum xs); lst p xs }}}` hands the list back and states the result; `listsum` uses it through `wp_call_bind`; 14 s, against 38 s for the spike on the old language |
| 3, rendering | dterm-rocq (another thread) | Iris notation and proof-mode states on the site |
| 4, the main build | [_RocqProject](../rocq/_RocqProject), nix/rocq.nix | Pieces.v, Heap.v, Language.v and Logic.v are part of the model, built and parse-checked by the quick gate with stdpp and Iris from the pinned nixpkgs; they add about 13 s of compile time off the critical path. The list-sum examples stay in spikes/ |
| 5, a program in the main build | [BufferLogic.v](../rocq/theories/programs/BufferLogic.v) | `buffer_never_panics` again, through the logic: the allocation's `obj` splits into `live` and four cells, each loop is a Löb induction carrying them, each check lends `live` back for a step and each access takes the one cell it reaches (`cells_at`). Without `live` in the sum loop, or with three cells, the proof fails. Needs no new rule: `buffer` has no named locals and checks only class `a`. 14 s, after `arith` learned to treat a remainder by a constant as a bounded variable before reaching for division equations (`mod_atoms`, `arith_fast` for side goals that may be false): BufferLogic.v 24 s to 18 s to 14 s, Cycle.v 6.3 s to 3.9 s, Buffer.v 10.4 s to 6.6 s and ListSumLogic.v 17.5 s to 13.1 s |
| 6, contracts | [Language.v](../rocq/theories/logic/Language.v), [Logic.v](../rocq/theories/logic/Logic.v), [ContractFrame.v](../rocq/theories/logic/ContractFrame.v) | the language takes a contract registry and a world: an admissible external call returns through Campaign 4's `invoke`, returns badly (`EBad`, never safe) or stalls (blocking, exit, resources); `adequate_labelled` and `heap_labelled_safe` prove the labelled machine's safety (no `failure_ending`, a return satisfies the postcondition) from a WP; `wp_external` is the call rule; the state interpretation gains a world interpretation `wi`, kept at safepoints (`SafepointStable`). The frame for a call: if a contract's writable roots share no address with the program's live owned objects and it releases none of them, the ghost heap still agrees after the whole effects path (`prefix_agrees`), and roots the call delegates stay apart (`delegates_apart`). Separation is by address, not identity, a premise of the program's theorem rather than of `puts_pre` (Campaign 4 agreed: formal.md promises no blanket input immutability) |
| 6, hi.c | [HiLogic.v](../rocq/theories/programs/HiLogic.v) | `hi_logic_safe` for every runtime and `interp_hi_logic_safe` from Hi.v's fixture, closed. The program owns its literal as a `string`; the world interpretation is `stdio_wi` (puts's rep, `stdio_ready`, the world's roots apart from the program's objects); puts is `wp_puts` from StringLogic.v; main is six tactic lines. No new rule was needed: main has no named locals and no check |
| 7, strings | [StringLogic.v](../rocq/theories/logic/StringLogic.v) | `string p b reg bytes`: the life of the object p's capability names, read-write or read-only, and its bytes through the NUL; owning it gives Campaign 4's `terminated_length` and `c_string` (`string_facts`), lends a suffix (`string_suffix`) or one byte (`string_byte`). Triples derived from the contracts, each stated at any call site: `wp_strlen` and `wp_strchr` (pure calls: memory and world unchanged, `pure_return`) over any registry and world, `wp_puts` under `stdio_wi` (the frame keeps the string through puts's writes). New rules: `wp_check_read`, a read check through an `Obj` or `Ro` capability, and `wp_raw_load_byte`, a one-byte load |
| 7, a read after a call | [ScanLogic.v](../rocq/theories/programs/ScanLogic.v), [scan.c](../rocq/theories/programs/scan.c) | `scan(s)` takes `strlen(s)`, finds the first `l` with `strchr`, prints the rest with `puts`, then reads the byte after the `l` through strchr's pointer: three calls and a read after the last one. `scan_logic_safe` for every runtime and `interp_scan_logic_safe` on Hi.v's fixture ("hello"), closed. The proof (`scan_spec`) is 43 lines: one rule per instruction, the three triples, and the facts that make the read safe: strchr's hit is before the NUL because `l` is not 0, so the byte after it is in the string the frame kept through puts. Still no named locals, so `wp_ret` needed nothing new |
| 7, a helper in a loop | [CountLogic.v](../rocq/theories/programs/CountLogic.v), [count.c](../rocq/theories/programs/count.c) | `next_l` is strchr for `l`, with its own triple (`next_l_spec`, 13 lines, from `wp_strchr`); `count_l` calls it once and then in a loop on the suffix past each hit, reading the byte each hit lands on. Both calls use the triple through `wp_call_bind`; the loop is a Löb induction at the head (`count_loop`, 46 lines) carrying the string and "the pointer is null or before the NUL" (`found_from`), re-established from the callee's postcondition on the suffix (`found_next`). `count_logic_safe` and `interp_count_logic_safe` (two `l`s in "hello"), closed; 5.3 s. No new rule: no named locals, so `wp_ret` is still the one without them. `gen_env` moved to Symbolic.v for both loop proofs |
| 7, writes, malloc and free | [MemLogic.v](../rocq/theories/logic/MemLogic.v), [Logic.v](../rocq/theories/logic/Logic.v), [Heap.v](../rocq/theories/logic/Heap.v) | a block of memory is owned piece by piece: `bytes b o xs` and `auxes b o cs`, its bytes and its aux slots. `wp_memset` from `memset_contract`: the block's bytes become c's low byte and every slot starting in it is emptied (`clear_slots`). `wp_memcpy` from `memcpy_contract`: a destination block and a source block in another object, both 8-aligned and so in phase; the destination takes the source's bytes, each full slot takes the source's capability and a partial one empties (`copy_slots`, `copy_after`); the source comes back unchanged. The contracts' exact destination frame keeps every other piece (`block_frame`, through Heap.v's `frame_within` for writes inside one live object). Blocks start at a multiple of 8, so the slots a write touches start inside them. `wp_strdup` from `strdup_contract`: owning a `string`, the call returns a fresh object owning a copy as a `string` (its other bytes and its slots unowned); its writes lie in the fresh object, so `frame_other` keeps the rest. `wp_string_copy` from `string_copy_contract`, with `wp_strcpy` and `wp_stpcpy` its instances: owning a destination's `live` and `bytes`, one more than a `string`'s in another object, the bytes become a `string` with the copy, d is bound to the destination or, for stpcpy, its NUL, and the source comes back; no slot is owned, since a scalar copy keeps every aux slot, and no alignment is needed (`copy_string_after`). `wp_malloc` from `malloc_contract`: the fresh object's pieces (`obj`), no null case, since the selected malloc refuses with a resource ending. Logic.v's `wp_free` gives up a heap object's `live`, whose ghost token ends as `VFreed` (the ghost heap cannot delete a key), and `wp_free_null`; both take `frees_heap` of the genv's free, which every runtime's free meets by Runtime.v's axiom `free_succeeds` (since 2026-11-09; the interpreter's `free_res_succeeds`). `wp_raw_store_byte` is new for a one-byte store |
| 7, a callee owning memory | [SlotLogic.v](../rocq/theories/programs/SlotLogic.v), [slot.c](../rocq/theories/programs/slot.c) | `fill(c, n)` keeps one heap buffer in its static `slot`, with its size in `slot_size`: if n does not fit it frees the buffer and mallocs n + 1 bytes, then memsets n bytes, writes the NUL and returns the buffer. The module invariant `slot_inv` owns both statics and the `buffer` they describe (null and 0, or a live heap object with all its bytes and slots). `fill_spec` takes the invariant and returns `lent`: the n filled bytes and a wand that, given them back, returns the invariant, so the caller cannot keep them across its next call. `use` calls `fill` three times (grow, reuse, grow) and reads the buffer after each. `slot_logic_safe` for every runtime, with no premise since `free_succeeds` became an axiom, `interp_slot_logic_safe` from the module's initial memory, closed; 14.8 s. Still no named locals: nanofil keeps `fill`'s and `use`'s locals in temporaries |

**hi.c, the logic against Hi.v's hand proof.** The same body, the same
contract, the same fixture:

| | Hi.v (hand) | HiLogic.v (Iris) |
| --- | --- | --- |
| size, non-blank lines | about 270 for the safety part: the literal's validity across safepoints, a step lemma per point, the four-phase invariant `hi_body_state` with a case per kind of labelled step | 312 when it stood alone: the literal as pieces and back (75), the world and puts's frame (44), puts's triple and main (65), adequacy (29), the interpreter instance (62); 196 once puts's triple and the frame moved to StringLogic.v |
| compile time | 1.2 s, the whole file | 5.8 s alone, 4.2 s on StringLogic.v; 1.1 s of either loads Logic and Hi |
| premises | `hi_before_call`, `stdio_stable` | those, and the runtime ready, live objects apart, the world's roots apart from the literal (`literal_apart`) |
| conclusion | every stop is one of `hi_ending`'s three, by name | no stop is a `failure_ending`, and a return is 0 |
| reusable | nothing outside hi | `wp_external`, the frame, `heap_labelled_safe`; the triple is stated at hi's site and literal |

For hi alone the logic does not pay: as long, five times slower to
check, more premises and a weaker conclusion. Hi.v gets away without a
frame because main reads nothing after puts, and its invariant has no
heap in it; the logic must re-establish its state interpretation after
every call, so it needed the frame theorem before it could prove a
program with one call. What it bought is where the cost lands: the
program-specific proof is six lines and stays a line per instruction,
while Hi.v's method adds a constructor and a case analysis per program
point and would need the same frame argument as soon as a program reads
memory after a call. The test of whether it pays is the next program
with a call it reads after: gc.ir's `sum` with a `c_gc` contract, or
Hello's first string call, with puts's triple generalised from hi's
literal to a `string p` assertion.

**scan.c, the read after a call.** The next program does read memory
after a call, so here the hand method would need the frame too. There
is no hand proof of scan; the hand column is an estimate from Hi.v's
rate, which is the method's only proof with calls:

| | Hi.v's method (estimate) | ScanLogic.v (Iris) |
| --- | --- | --- |
| program points | 15 (6 in `start`, 2 in the miss, 7 in the hit), 3 calls, a branch | the same |
| program-specific proof | Hi.v's body section is 187 non-blank lines for 4 points and 1 call, about 45 a point: 600 to 700 lines for scan, plus a memory-level frame for puts (the string's region and bytes kept through its writes, from ContractFrame.v's segment lemmas) and the string's validity across safepoints | `scan_spec` 43 lines, `scan_logic_safe` 21; the file is 215 non-blank lines, of which the module, blocks and registry are about 90 and the interpreter instance about 25 |
| shared, written once | none: each program's invariant restates what each call needs | StringLogic.v, 438 lines: strings as pieces and their reading as Campaign 4's strings (183 pure, 44 in Iris), the stdio world and puts's frame (58), the three triples and the pure-call lemma (153: `wp_strlen` 28, `wp_strchr` 47, `wp_puts` 28); Logic.v gained `wp_check_read` and `wp_raw_load_byte` |
| compile time | Hi.v's 1.2 s for 4 points; scan's would be several times that | ScanLogic.v 5.6 s, StringLogic.v 4.8 s |
| conclusion | every stop named | no stop is a `failure_ending`, a return is an int |

This is where the logic starts to pay: scan's own proof is a fifth of
the estimate for the hand method, and the triples behind it are already
used twice (hi.c now takes `wp_puts` from StringLogic.v and shrank from
312 to 196 lines). The price is a fixed one, StringLogic.v and the
contract machinery in Language.v and Logic.v, and compile time, which
stays above the hand method's. The case for the hand method is now only
programs with no read after a call.

**count.c, a helper with a triple in a loop.** The two things Hello
needed that scan did not: a callee's specification used by its caller,
and a call inside a loop. The hand method has no callee
specifications: its invariant covers every configuration, so the
callee's points appear once per call site with the caller's frame
under them, and the loop needs its invariant at the head as well.
Again an estimate from Hi.v's rate:

| | Hi.v's method (estimate) | CountLogic.v (Iris) |
| --- | --- | --- |
| program points | 16 in `count_l`, 3 in `next_l` at each of 2 call sites | the same, with `next_l` proved once |
| program-specific proof | about 22 configurations at 45 lines: 900 to 1,000 lines, plus the string's validity across safepoints | `next_l_spec` 13, `count_loop` 46, `count_spec` 14: 73 lines; the file is 263 non-blank lines, most of it the module, blocks and the interpreter instance |
| what carries over | nothing | `next_l_spec` is used at both calls; the loop invariant is three facts and the string |
| compile time | several seconds at Hi.v's rate | 5.3 s |

The callee's triple is what keeps the proof small: each call is one
application of `next_l_spec`, and the caller never sees strchr. Hello's
next needs from the table below are memory-writing contracts (Campaign 4
has started with memset), and a callee that owns memory across calls.

**slot.c, a callee that owns memory across calls.** quotearg's shape:
the callee's state lives in static objects between calls, the heap
buffer they point to changes identity when it grows, and the caller
reads a result it must not keep. Again against Hi.v's rate:

| | Hi.v's method (estimate) | SlotLogic.v (Iris) |
| --- | --- | --- |
| program points | `fill` 37 (6 at its entry, 13 growing, 18 filling), `use` 22; `fill`'s appear at each of its 3 call sites, with the buffer in a different state each time | the same, with `fill` proved once for any c and n |
| program-specific proof | about 130 configurations at 45 lines: 5,000 lines or more, plus a heap-level invariant relating the statics to the buffer, which Hi.v's state machine has no place for | `fill_L6` 55 and `fill_spec` 60 (the two paths of `fill`), `use_spec` 33, the invariant and lending 12, splitting bytes and freeing the buffer 40: about 200 lines; the file is 510 non-blank lines, of which the module, blocks and interpreter instance are most of the rest |
| shared, written once | none | from MemLogic.v: blocks as pieces (60), the frame and memset's effect on them (`block_frame`, `fill_after`, 90), `wp_memset` 63, `wp_malloc` 50; `wp_free` and `wp_raw_store_byte` in Logic.v. MemLogic.v also has `wp_memcpy`, `wp_strdup` and the string copies, which slot.c does not use |
| compile time | well above a second per call site | SlotLogic.v 14.8 s (`fill`'s two lemmas about 4 s each, `use_spec` 3.5 s), MemLogic.v 3.2 s for memset and malloc, 5.1 s with memcpy and strdup, 6.6 s with strcpy and stpcpy |
| conclusion | every stop named | no stop is a `failure_ending`, a return is an int |

The invariant is what the hand method lacks: the state `fill` leaves for
its next call is a separation-logic assertion, so the second call needs
nothing about the first beyond `slot_inv`, and the caller's reads are
safe because it holds the bytes the triple lent. The wand in `lent` is
quotearg's contract with its caller: the buffer is valid until the next
call. Writing it needed one fact Runtime.v did not state, that free
succeeds on a live heap base and on null (`frees_heap`). It was a
premise of `slot_logic_safe` until mbrock made it an axiom,
`free_succeeds`, with a native test (axiom-free-succeeds.c).

The premise `keeps_live` is gone: only a signal handler the program installed, or a thread it
started, frees a live object, so Runtime.v's safepoint axiom is now the
collector's alone, `collector_live`, which makes `keeps_live` a lemma.
Handlers are program code, to be verified under an ownership
invariant.

## What Hello will demand

From the proposal, with what Campaign 4's contracts would need to say
for each (the contracts stay relational and trusted; a triple is
derived from each once):

| Need | Assertion | What the libc contract must state |
| --- | --- | --- |
| gnulib's string code | `string p`: identity, offset, `live`, a NUL at or after it | for each pointer argument, the bytes it reads up to a NUL; for each result, which identity it points into |
| `__ctype_b_loc` | a persistent table from −128 to 255: persistent `meta`, `live` and read-only cells | that the returned object is never freed and never written |
| `malloc`, `strdup` | `obj b q`, then `live b`, `bytes` and `auxes`: zeroed or copied cells | the extent of the new object; nothing else changed. Done: `wp_malloc`, and `wp_strdup` as a fresh `string` |
| `free` | consumes `live b` | that it frees only its argument's object. Done (`wp_free`), from the axiom `free_succeeds` |
| quotearg | a slot invariant, with the result lent: `string ret ∗ (string ret −∗ slots)` | that a buffer it returns is valid only until the next call with the same slot that grows it. Shown on slot.c (`slot_inv`, `lent`) |
| exit, atexit | the registered functions' specs, by case on the pinned targets | the order and set of callbacks (Campaign 4's registry) |
| every call | the frame rule | the writable roots and nothing beyond them: no write, free or capability change outside the footprint |

## GNU Hello through the logic

The target (mbrock, 2026-11-09): `never_panics` of `nanofil-hello-O`,
proved through the Iris logic as scan, count and slot were. Campaign 4
writes the libc contracts, the entry and exit's callbacks; this
campaign writes the triples and the program's proof.

**The program.** [HelloModule.v](../rocq/theories/hello_contracts/HelloModule.v) reads
Hello as one checked module, `hello_module`. Its fixture,
[HelloCode.v](../rocq/theories/hello_contracts/HelloCode.v), is what
[link.pl](../rocq/scripts/link.pl) makes of the 81 checked terms of the real
build, regenerated and compared by the flake check
`nanofil-hello-fixture` (`rocq/scripts/hello-fixture.sh`):

- each object's `local` names become `OBJECT#NAME`, because objects
  reuse them (closeout.o and hello.o both have a `str.54`);
- exported names are shared, and each is defined once;
- only the items a run from `main` can name, through a `global(S)`
  operand or a `sym(S, Off)` data item, are kept: 32 functions and their data, 183 KB of IR. Leaving
  the rest out changes no run, since no run can name them. This is a
  claim about the link that no Rocq lemma states yet.

Every object was valid alone, and the link is valid too
(`hello_valid`). That needed one fix to [gallina.pl](../rocq/scripts/gallina.pl): a byte from 128 to
255 in a string now prints as its two UTF-8 bytes, as Term.v's
`char_code` reads it. Before the fix, gettext_quote's `‘` decoded to an
unknown item and the link was `Some false`. HelloCode.v compiles in
9 s, and HelloModule.v in 20 s, of which `vm_compute` of `valid` takes
8.5 s.

**What it calls.** `hello_externals_exact` lists the 33 libc functions
the module calls. They are the plain entries, not the fortified ones:
`printf`, `fprintf`, `wprintf`, `fputs`, `atexit`, not
`__printf_chk`. Seven of them are called only by quotearg
(`iswprint`, `mbrtoc32`, `__ctype_b_loc`, `__ctype_get_mb_cur_max`,
`mbsinit`, `zmemmove`, `realloc`). Quotearg is reached only through
close_stdout's diagnostic for a named file, and Hello never names one:
closeout's static `file_name` stays null. A module invariant over that
static rules the branch out, so its 414-block function needs no
triple. Without it, 21 functions remain (about 200 blocks):

| Group | Functions | Contracts |
| --- | --- | --- |
| startup and options | `main` (25 blocks; parse_options and print_help are inlined), `set_program_name`, `memeq`, `mbszero` | `strrchr`, `memcmp`, `strncmp`, `memset`, `setlocale`, `atexit`, `getopt_long`, `strlen`, `malloc`, `wprintf`, `free`, `exit`, `fprintf`, `fputs` |
| the greeting's conversion | `rpl_mbsrtowcs` (29), `rpl_mbrtowc`, `hard_locale`, `setlocale_null_r` and its two helpers, `streq`, `strnlen1`, `xmalloc`, `xalloc_die` | `mbrtowc`, `setlocale`, `memcpy`, `strlen`, `strcmp`, `memchr`, `error`, `abort` |
| `--version` and `--help` | `version_etc`, `version_etc_va`, `version_etc_arn` (27), `emit_bug_reporting_address`, `proper_name` | `fprintf`, `fputs`, `printf` |
| the ending, as exit's handler | `close_stdout`, `close_stream` | `__fpending`, `ferror`, `fclose`, `__errno_location`, `error`, `_exit` |

`abort` has no contract: reaching it is a failure, so the proof must
show that rpl_mbsrtowcs and xalloc_die never reach it. xalloc_die is
reached only when malloc returns null, which the selected malloc never
does.

**Decisions** (mbrock, 2026-11-09):
- The link keeps what is reachable from `main`, as above. A later Rocq
  lemma will show that `find_fn` agrees with the full link on every
  reachable name.
- `abort` stays without a contract, so reaching it is a failure: the
  proof shows that Hello never calls it.
- Every path is proved, `--help`, `--version` and the error paths
  included, the default path first.

**Milestones.**

1. Done: the linked module, its gate, `hello_valid`, and the external
   list.
2. Done: leaf triples from contracts that exist, then
   `set_program_name`. See "Milestone 2" below.
3. Done: the conversion chain, over a locale the world interpretation
   holds, up to `rpl_mbsrtowcs_spec`. See "Milestone 3" below.
4. In progress: `main` and its option loop, from Campaign 4's entry. This needs
   `setlocale`, `atexit`, `getopt_long`, `wprintf` and `exit`.
5. `close_stdout` as exit's callback, through Campaign 4's Linked.v
   bridge, which runs an ordinary callback frame.
6. The `--help`, `--version` and error paths.
7. `never_panics` of the linked module from the entry.

**Milestone 2.** New libc triples:
- [LibcStringLogic.v](../rocq/theories/hello_contracts/LibcStringLogic.v) retains `wp_strcmp`,
  `wp_strncmp` and `wp_strrchr`.
- [LibcMemLogic.v](../rocq/theories/hello_contracts/LibcMemLogic.v) retains `wp_memcmp` and
  `wp_memchr` over blocks read through read-write or read-only
  capabilities. Their shared helpers `block_readable` and `string_window`,
  which lends n bytes of a string as a block, remain in
  [MemLogic.v](../rocq/theories/logic/MemLogic.v).
- Logic.v gains `wp_ret_void` for `void` functions.

[HelloLeaf.v](../rocq/theories/hello_contracts/HelloLeaf.v) (12 s, 7 s of which is
laying out the module's 115 symbols) proves `mbszero_spec`,
`memeq_spec`, `streq_spec` and `strnlen1_spec`. They hold in any genv
that links Hello (`hello_linked`): its module is `hello_module`, its
symbols include Hello's own, and no libc function Hello calls is a
symbol. The registry and the world interpretation are any that hold
the contracts, so the same triples serve the whole program over
Campaign 4's world. A caller binds them through `wp_call_bind` at
`invocation f xs`, the frame `call_frame` makes.

[HelloName.v](../rocq/theories/hello_contracts/HelloName.v) (15 s) proves
`set_program_name_spec` on every path:
- The function owns argv[0] as a string, the two literals "/.libs/"
  and "lt-", and three cells: Hello's `program_name` and libc's
  `program_invocation_name` and `program_invocation_short_name`, each
  its own object, as each Fil-C global is.
- Whatever memcmp and strncmp return, the run is safe. The cells end
  up holding pointers with argv[0]'s capability, the first two the
  same one.
- Each store's premise, that it keeps the world interpretation, is
  `store_keeps`, which Campaign 4's world must show for the three
  cells.

The compiled function has no null check of argv[0]. gnulib declares
the parameter nonnull, so clang drops the abort branch. The
never-panics theorem therefore needs argc ≥ 1, which Startup's
`startup_at` gives.

Two lessons on cost:
- `vm_compute` of a goal that names `hello_module` is fast, but `cbn`
  or `discriminate` on one unfolds the whole decoded module (minutes).
  The proofs only compute module facts through `vm_compute`
  (`outside_find`, `hello_outside`).
- `put` on an abstract environment needs `gen_env` before a lookup
  through it reduces.

**Milestone 3, so far.** The locale helpers are proved. Still to come
are `rpl_mbrtowc` and `rpl_mbsrtowcs`, which wait on Campaign 4's
mbrtowc, errno and composite-world contracts. New in the logic:
- Logic.v adds `wp_renew` and `wp_half_check_read`. The second is a
  read half check through a read-only capability, as rpl_mbsrtowcs
  makes on the greeting literal. MemLogic.v adds `wp_raw_store_w`,
  the 4-byte store with which rpl_mbrtowc's fallback writes `c: *pwc`.
  It also adds `bytes_app`, `auxes_app` and `obj_zero_block`, which
  read a fresh object as a block.
- [HelloLeaf.v](../rocq/theories/hello_contracts/HelloLeaf.v) adds `xmalloc_spec`:
  the selected malloc never returns null, so `xalloc_die` is dead.
- LibcMemLogic.v retains `wp_memchr_string`, a search for the NUL in an
  owned string with any bound. Campaign 4's memchr reads only through
  its first match (25073c1), so the bound may run past the string's
  object; `memchr_input_bounded` reads the admission off the string's
  `bounded_length`, and the result is `nul_found`: the NUL if the
  string is shorter than the bound, else null. On it, `strnlen1_spec`
  now returns exactly min(length + 1, n). rpl_mbsrtowcs calls
  `strnlen1(p + 4, 12)` on the greeting to size its mbrtowc window, and
  the audited codec profile rules out -2 by that size or its NUL. The
  milestone 2 version over a whole block, whose result was any int, is
  gone.

**Strings the world lends.** setlocale(k, NULL) returns libc's own
name for category k. The program does not own that memory, and a
weakest precondition cannot remember across steps which string a query
returned, because the memory and the world belong to the state, not
to the assertion. Pieces.v therefore gains a ghost piece, `PName k`,
valued `VName p t`. It names no memory: `mem_piece` is false for it,
`owned_live` and `ids_apart` skip it, and it agrees with every memory.
The world interpretation ties it to the world. An Oracle review chose
this over a world-indexed state interpretation, which would have
changed `heap_interp` and about 23 proof sites.
[LentLogic.v](../rocq/theories/hello_contracts/LentLogic.v) (4 s) reads such a string
through `lent k p t`, a persistent token. It carries what holds of the
lent value from the moment it is lent: p is not null, t ends before
2^64, and t's bytes are not NUL. It needs one fact of the world
interpretation, `lent_at`: the string is a C string, in an 8-aligned
object (Campaign 4's `locale_name_aligned`, f9a82b6), apart from every
object the program owns. On that fact it proves:
- `wp_lent_query`, for a call that returns the lent pointer and
  changes nothing, such as setlocale's query;
- `wp_strlen_lent`;
- `wp_memcpy_lent`, for a prefix of the name with its NUL, copied
  into an owned block. The block's aux slots afterwards are whatever
  the copy left (`slots_after`), since the source's slots are libc's.

Before a name is lent it is owned whole, as `named k p t`. The setter
setlocale(LC_ALL, "") takes the names it changes: `wp_lend` renames
them in the ghost heap (`rename_update`) and hands back persistent
`lent` tokens for the new names, whose facts it reads off `lent_at` in
the state after the call. What the call must keep of the state, its
frame and wi of the renamed heap, is the triple's premise, for the
contract and the world interpretation to discharge.

[LocaleLogic.v](../rocq/theories/hello_contracts/LocaleLogic.v) gives the world
interpretation of a program that calls setlocale, `locale_wi`, over
Campaign 4's `locale_world`:
- the world is `locale_ready`;
- libc's roots and the objects it may release are apart from the
  program's pieces, as the frame of an external call needs;
- the object of every read, root and name capability owns no piece
  of the program (`cap_private`);
- every ghost name is its category's current name (`names_current`).

From it, `locale_wi_lent` is LentLogic's `lent_at` for every ghost
name. A name is a C string in a live object (live because a freed
object is empty and a C string is not), and that object is private,
so no live object of the program overlaps it. `locale_wi_pre` and
`locale_wi_query` discharge HelloLocale's premises on setlocale's
query. `wi_lent` now also takes the facts a ready runtime gives:
live objects apart, objects in the address space, and freed objects
empty.

A setter keeps `locale_wi`, with every category renamed to its new
name (`locale_wi_setter`). The frame keeps libc's old roots apart from
the program; the new roots have write authority only from old roots
or born objects, so they stay apart. Campaign 4's private provenance
(`locale_delegates_private`, 4de6b80) makes every new read, root and
name capability a born object, which is none of the program's, or an
old private one. `locale_set_return` states this for setlocale(c, p)
in the form of `wp_lend`'s premise, and `wp_setlocale_set` is the
setter's triple over the locale world: owning every category's
`named` token and the string argument, the call binds null or c's new
name and lends every new name for good.

Two findings went back to Campaign 4:
- The setter contract let a new name carry the setter input's
  capability, or one loaded from a source's aux slots. A name could
  then lie in the program's own literal, and no apartness would hold.
  Campaign 4 restricted new names, reads and roots to born objects
  or the exact capability of an old read, root or name (4de6b80),
  which is what the setter's discharge of `wp_lend` needs.
- `Locale R`, `Libio R`, `Startup R` and `ExitMemory R` each built
  their own `ExternalCalls R`, whose `invoke` is a different inductive
  from the logic's `M.E.invoke`, so their theorems could not be
  applied in the logic. Campaign 4 added exact-machine variants
  (b03f7ec): `LocaleOn R M` and its siblings take the machine module
  itself, and LocaleLogic instantiates `LocaleOn R L.M`, so
  `locale_wi_query` now uses `setlocale_query_invocation` directly.

[HelloLocale.v](../rocq/theories/hello_contracts/HelloLocale.v) (17 s) proves
`setlocale_null_unlocked`, `setlocale_null_r_unlocked` on both of its
paths, `setlocale_null_r` and `hard_locale`:
- If the name fits in the buffer, it is copied with its NUL and the
  result is 0.
- Otherwise its first n - 1 bytes are copied, a NUL follows, and the
  result is ERANGE (`snru_result`).
- The NULL path, EINVAL, is dead because a lent name is never null.
- `hard_locale` copies the name into a fresh 257-byte buffer and
  compares it with "C" and "POSIX". Whatever strcmp answers, the run
  is safe.

The triples take setlocale's query as premises on its contract
spec, so they serve Campaign 4's composite world once its lifted
setlocale contract shows them. The same holds for the premises that
the world interpretation survives the allocation, the copy and the
byte store. The token is persistent, so no triple changes a lent
name. Hello's one setter, setlocale(LC_ALL, ""), runs before any
query. Its triple, `wp_setlocale_set` above, takes the names owned
whole and turns them into the persistent tokens.

Two more decisions shape the rest of the milestone:
- Hello's conversion theorem carries an explicit premise that the
  codec is one of the audited C or C.UTF-8 profiles (mbrock,
  2026-11-09). It is not derived from `locale_ready`, from a
  successful setlocale, or from MB_LEN_MAX. Campaign 4 found that an
  arbitrary stateful codec does not justify the -2 restrictions that
  rule out `abort`.
- `__errno_location` now has a contract (Campaign 4, ff21058), for
  rpl_mbsrtowcs's EILSEQ store.

**Pieces proved in parallel.** From milestone 3 on, helper threads
own pieces in their own files and hand them over for integration
here. Each is generic in the registry and the world interpretation,
and takes as Context premises the contracts that Campaign 4's
packages are still landing.
- [HelloProgName.v](../rocq/theories/hello_contracts/HelloProgName.v) (5a34c2f)
  strengthens HelloName's `set_program_name` triple, which only knew
  capabilities, to bounded suffixes of the owned argv[0] string.
  `set_program_name_string_spec` lends the chosen `program_name`
  suffix as a string, with a wand that restores argv[0], ready for
  printing. The one new comparison fact is `strncmp_zero_lengths`: a
  zero from strncmp means equal bounded lengths, so comparing with
  "lt-" for three bytes justifies advancing three without crossing
  the NUL.
- [CallbackLogic.v](../rocq/theories/hello_contracts/CallbackLogic.v) (9a11a87)
  connects a handler's weakest precondition to Linked's void-callback
  endpoint. `callback_wp_safe` rules out failure endings for every
  labelled run. `callback_wp_return` gives the handler's
  postcondition at the exact memory after `invalidate_locals` and at
  the current world, before ReturnCallback. It rests on
  `heap_exact_adequacy`, an adequacy that keeps the final state,
  where `heap_labelled_safe` forgets it.
- [HelloReach.v](../rocq/theories/hello_contracts/HelloReach.v) (c37f796) checks
  reference closure of the linked image. From main, static
  reachability follows global addresses and initializer symbols,
  including callbacks. Every reachable reference is a module function,
  a module global, one of 33 libc function imports, or one of six
  libc data imports: stdout, stderr, optarg, optind,
  program_invocation_name and program_invocation_short_name.
  `hello_genv` keeps the module's globals as a prefix, so startup
  data cannot override a module symbol, and `hello_genv_linked`
  proves `hello_linked`. The proof is about the image we run. That
  the linker's pruning kept every reachable definition of the
  original objects is trusted, checked by the linker's own traversal.
- [HelloVersion.v](../rocq/theories/hello_contracts/HelloVersion.v) (471c501,
  dac4525) proves `proper_name`, the identity, and the help footer
  `emit_bug_reporting_address`. The footer's literals stay owned by
  the program; stdout is the world's cell. Its four output calls take
  premises that line up with Campaign 4's Formatting.v contracts.
  It also proves the version chain `version_etc`, `version_etc_va`
  and `version_etc_arn` for the one call main makes
  (`version_main_args`): the stream, the package, program and version
  literals, four author pointers that are `proper_name`'s results, and
  a null. The other author counts are unreachable, since nothing else
  calls the chain. `version_etc_va` derives the count of four by
  running its loop's five va_arg reads over the snapshot; the count is
  not a premise. The six output calls keep the program's literals on
  success, partial and negative output alike. The snapshot's
  allocation, the stores into the author array and the cursor update
  are world-frame premises (`Kversion_*`), and the output contracts
  are raw premises like the footer's.

- [HelloClose.v](../rocq/theories/hello_contracts/HelloClose.v) (2a1f328) proves
  `close_stream` and `close_stdout`. `close_stream` consumes a usable
  stream, follows the pending, error and fclose decisions (EBADF
  included), and returns 0 or EOF, handing back the four errno bytes.
  `close_stdout` owns its statics: `file_name` stays null and
  `ignore_EPIPE` zero, so the `quotearg_colon` branch is dead and no
  quotearg triple is needed. It closes stdout, then stderr. A stdout
  failure calls `error` with status 0, then `_exit`; a stderr failure
  calls `_exit` directly. Wiring it as exit's callback, and `_exit`
  over the exact machine, remain integration work.

Conventions the pieces share:
- Module statics and the cells the program reads or writes directly
  are owned pieces passed into the calls that write them, never facts
  of wi. That covers file_name, ignore_EPIPE, program_name, errno,
  optind and optarg.
- A contract enters as raw premises: registry, ABI, admission, and
  what an invocation keeps. Call-site triples are derived from them
  with `wp_external`.
- A rule a piece needs and the core lacks stays in the piece, marked
  for promotion, until it is reviewed into Logic.v. The candidates so
  far:
  - `wp_strncmp_lengths`;
  - `heap_exact_adequacy` and the Linked transports;
  - `rule_va_args` and `wp_va_args`;
  - `rule_va_arg`, `wp_va_arg` and `wp_va_arg_pointer`, the cursor
    read; `rule_snapshot` and `wp_snapshot`, the va snapshot's
    allocation;
  - `wp_raw_load_literal`, a pointer load from a read-only literal,
    which needs an Oracle review of its capability reasoning before
    promotion;
  - `wp_world_let`, a load whose value wi fixes;
  - `wp_close_errno`, `wp_close_load_w`, `wp_close_contract` and
    `wp_close_stream_pointer`.

**The conversion chain, first step.** mbrtowc writes three cells the
program owns: the wide character, the conversion state and errno.
Its roots therefore meet the program's objects, and the external
call frame, which needed roots apart from every owned object, did not
apply. [ContractFrame.v](../rocq/theories/logic/ContractFrame.v) now has a
frame for calls into owned blocks (54dc057): `agrees_except`,
`roots_out` and `pieces_off` say that the roots touch owned objects
only at the addresses the program hands over, and that no other piece
lies there. `local_agrees_out` and Logic.v's `effects_agrees_out` and
`prefix_agrees_out` keep every other piece agreeing.
`local_agrees` and `effects_agrees` are now the case where nothing is
handed over, with the same statements as before.

[HelloConv.v](../rocq/theories/hello_contracts/HelloConv.v) proves `wp_mbrtowc` over
Campaign 4's `libc_world`, using `LibcOn R L.M`. The program hands
over the three cells as whole blocks (life, bytes and aux slots) and
lends the source bytes. The call gives the blocks back holding
whatever memory holds afterwards. `conv_result` reads
`mbrtowc_result` through the owned bytes under the audited codec:
- a NUL converts to 0 and resets the state;
- a character of r bytes, none of them NUL, becomes a nonzero wide
  character;
- EILSEQ stores 84 in errno and leaves the output alone. Under the C
  codec it also keeps the state and starts at a byte of 128 or more
  (`mbrtowc_c_error`);
- an incomplete sequence is shorter than 16 bytes, with no NUL.

The world interpretation must make libc ready with a fixed errno
cell. It keeps libc's private roots, releases and capabilities apart
from the program's objects (`libc_private`), and it must survive the
call's writes into the three blocks. The audited codec stays an
explicit premise.

The codec is not fixed for the whole run: Hello calls
`setlocale(LC_ALL, "")` before it converts, and that call may select
another codec. A conversion therefore learns the codec from a ghost
piece. The ghost heap gains a value `VCodec c`, which, like a name,
agrees with every memory, under the key `codec_key`, which is no
category's. `locale_wi` now also says `codec_current`: that piece
holds the world's codec. `wp_lend` takes extra ghost pieces that a
setter updates in the same step, so `wp_setlocale_set` takes the codec
piece and hands it back holding the codec the setter selected
(`relocale`). `wp_mbrtowc` takes the piece at any fraction, so after
setlocale it can be made persistent and shared by every conversion,
and the state stays valid under one codec from call to call.

Two contract gaps went back to Campaign 4, and it fixed both
(6e82502):
- Nothing kept the state's bytes in 0 to 255 after a call, so the
  second call of rpl_mbsrtowcs's loop could not be admitted. The
  contract now requires `mbstate_valid_bytes`: valid states hold
  bytes.
- Under the C codec, `hard_locale` is false, so rpl_mbrtowc's fallback
  turns EILSEQ into a one-byte character and the loop calls mbrtowc
  again with the same state. The EILSEQ state was unspecified, which
  would have made that call stuck. For the audited C codec only,
  EILSEQ now keeps the entry state and requires a first byte of 128
  or more, so ASCII and NUL never take it.

**gnulib's rpl_mbrtowc.** Hello never calls mbrtowc directly. It calls
gnulib's wrapper, which converts into the caller's pointer or, when
that pointer is null, into a fresh four-byte local. After an invalid or
incomplete sequence (an answer of 2^64-1 or 2^64-2) it asks
`hard_locale(LC_CTYPE)`. Outside a hard locale, the first byte stands
for itself: the wrapper stores it as the wide character and returns 1.
HelloConv.v proves this with two lemmas:
- `rpl_tail` covers everything from block L11 on: the call through
  `wp_mbrtowc`, then HelloLocale.v's `hard_locale_spec` on the failure
  path. `hard_locale` may answer either way, so both branches are
  proved.
- `rpl_mbrtowc_spec` enters with an output block the caller owns.

Only rpl_mbsrtowcs's converting loop reaches rpl_mbrtowc from main.
Main passes a fresh non-null buffer, so the counting loop, which passes
a null pointer, is never reached, and neither is the null entry.

`rpl_result` states what the caller learns: either mbrtowc's own
`conv_result`, or 1 with the first byte stored, after a failure that
left the output alone. The -2 case of `conv_result` keeps its premise
(n below 16, and no NUL in the n bytes), so a caller that counts n
through a NUL can rule it out. That is how rpl_mbsrtowcs's `abort`
becomes unreachable even in a hard locale.

**rpl_mbsrtowcs's converting loop.** For each character, the loop picks
a window of n bytes for rpl_mbrtowc. It reads up to four bytes,
stopping at the NUL, and then asks strnlen1 for at most twelve more.
`mbs_window` proves that n = min(len + 1, 16) for the string suffix at
the cursor, on all five paths.

`rpl_step` turns one call's `rpl_result` into what the loop needs. The
call is never incomplete, so the `abort` after -2 is not reached:
- -2 would need n below 16 and no NUL among the n bytes;
- n below 16 means the window reaches the NUL.

EILSEQ stores 84 in errno. The NUL stores a zero character. Anything
else consumes 1 to len bytes before the NUL, stores a nonzero
character, and leaves the state valid and in its initial shift state
(its first four bytes zero).

The fallback after EILSEQ needs the same facts under C.UTF-8. Campaign
4's `mbrtowc_initial_error` gives them: from a valid initial state, an
EILSEQ keeps the state valid and initial, and its first byte is not
NUL. `conv_result`'s EILSEQ case now carries that law.

`mbs_loop` proves the loop from block L28 by Löb induction. Its
invariant:
- i characters written from the first j bytes, with i ≤ j ≤ len;
- the written words are nonzero (`wide_ok`);
- the rest of the destination is owned, word by word;
- the state is valid and initial.

There are three exits:
- EILSEQ in a hard locale: the cursor is stored back through srcp,
  errno gets 84 (`wp_conv_errno`, a libc_world copy of HelloClose's
  rule, for promotion), and the loop returns -1;
- the NUL: null is stored through srcp, and the loop returns i, after
  i nonzero characters and a zero one (`mbs_post`);
- otherwise both cursors advance and the loop goes round.

The count left, len - i, never reaches zero before the NUL, because
i ≤ j ≤ len. Main reads the result as a wide string with
`wprintf("%ls")`, or calls `error` on -1.

`rpl_mbsrtowcs_spec` adds the entry, from start to L28, and so proves
the whole call as main makes it: dest a fresh buffer of len wide
characters, srcp a cell holding the string, len its length with the
NUL, and ps main's own state, not null, valid and initial. The entry
allocates a local only the counting loop uses, keeps ps, loads the
string through srcp, and enters the loop with nothing written. The
string may be a read-only literal. Logic.v's `wp_raw_load_pointer_in`
loads any pointer, read-only literals included. It promotes
HelloVersion's `wp_raw_load_literal` after Oracle review:
- the cell may be reached through a read-write or a read-only
  capability;
- the life of the object the loaded capability names is any
  `(PLive xb, VLive xr)` among pieces the caller already owns;
- capabilities for no object, a function or an external need no life.

Its proof rests on Pieces.v's `aux_holds_kept`: a stored capability
whose object is not freed is exactly what the slot holds.
`wp_raw_load_pointer` stays as it is for its callers. In
rpl_mbsrtowcs the life of the greeting's object is the head piece of
its `SL.string`, so the load needs no new token.

**Stream tokens.** The ghost heap gains a value
`VStream p pending` for Campaign 4's stream adapter. Its key is a
name, and `pending` is `Some (count, fifo)` while the stream is open
and `None` once it is closed. Like a codec, it agrees with every memory,
and only the world interpretation reads it. It is not a `VName`, so
`lent_current`, which constrains every `VName` in the heap, says
nothing about it. A stream's handle keeps its own `PLive` piece.

**One logic for main.** Two applications of `Logic R` have distinct
expressions, states and step relations, so triples proved over
separate instances cannot be combined. Before this change each Hello
file built its own chain from `R`, and so did `LocaleLogic R` and
`CallbackLogic R`. Logic.v now has a module type, `LogicSig`, the
signature of one instance. Each layer above it is a functor over one
instance, `XOn (R : Runtime) (LG0 : LogicSig R)`:
- StringLogic, MemLogic, LentLogic and LocaleLogic;
- HelloLeaf, HelloLocale, HelloConv, HelloName, HelloProgName,
  HelloClose and HelloVersion;
- CallbackLogic.

Inside each, `Module LG := LG0.` keeps the old paths. `X` itself is
`XOn` over a `Logic R` of its own, so no statement and no existing
user changes. Main's proof applies every `…On` functor to one
instance. Campaign 4's
StreamFrameLogic has the same signature, so its `…On` modules take
the same instance.

**Main's start block.** [HelloMain.v](../rocq/theories/hello_contracts/HelloMain.v)
applies every `…On` functor to one `Logic R`. Its world is libc's, and
its world interpretation wi stays abstract. Each section premise is
what one call needs of wi, so a concrete interpretation discharges
them once:
- `Kalloc`: an allocation keeps wi;
- `Kmemset`: zeroing eight owned bytes keeps wi;
- HelloName's cell layout and store premises;
- `Hlent`, `Hset_pre` and `Kset` for setlocale.

`wp_main_setlocale` is setlocale's triple over libc's contract,
`libc_setlocale_contract`, from LentLogic's `wp_lend`. It is the
libc-world counterpart of LocaleLogic's `wp_setlocale_set`, whose
world is the locale world alone.

`main_to_setlocale` proves main's start block from the entry up to
setlocale's call, and the triples of three files compose in it:
1. two fresh objects, b4 for the greeting's cell and b6 for the
   conversion state;
2. `mbszero` on b6 (HelloLeaf);
3. argv[0] loaded through `wp_raw_load_pointer_in`, its life the head
   of its string's pieces;
4. `set_program_name` (HelloProgName);
5. the literal "" copied.

`main_start_rest` proves the rest of the start block:
1. setlocale(LC_ALL, "") through `wp_main_setlocale`;
2. the default greeting stored in b4's cell (`Kpstore`);
3. atexit(close_stdout). Its contract stays abstract: it returns an
   int and keeps the program's pieces and wi (`Katexit`), because the
   registration is libc's own state.

`main_start` composes the two segments. It goes from main's entry to
the option loop's first block, with every resource the loop needs:
argv, the name cells, the lent names and the codec, the greeting's
cell and the zeroed state.

Next is the option loop. GNU getopt_long may permute argv, and main
reads `optind` and `optarg`, which are libc's cells, directly. So the
loop needs a getopt triple that takes argv's cells and hands them back
permuted, and a world-justified read of libc's cells.

**Reading getopt's cells.** Main owns neither cell, and getopt
rewrites both at every call. A ghost value, `VGetopt optarg optind`
under the name key 64, stands for what getopt last left there. Like
the codec and stream tokens, it agrees with every memory.
[GetoptLogic.v](../rocq/theories/hello_contracts/GetoptLogic.v) ties it to the world
through one premise on wi: the world's getopt state is in memory at
the two cells (Campaign 4's `getopt_state_at`), and the token is
current (`getopt_current`). Logic.v's `wp_world_let_with` is an
instruction whose result wi fixes given pieces the program owns.
GetoptLogic derives four rules from it:
- `wp_optarg_check`, optarg's 8-byte read check;
- `wp_optarg_load`, the pointer load giving the token's optarg;
- `wp_optind_check`, optind's 4-byte check at alignment 1;
- `wp_optind_load`, the signed 32-bit load giving the token's optind.

Campaign 4 added getopt state to `libc_world` (`libc_getopt`, viewed
by `libc_getopt_view`) and canonical byte bounds to `getopt_slots`
(1b61cc0). Without that state, any view would be constant, and getopt's
post would claim the cells never change. Campaign 4 also confirmed that
the registry can be fixed per launch after startup fixes argv, which
`getopt_contract`'s input needs.

**getopt_long's call.** [HelloMain.v](../rocq/theories/hello_contracts/HelloMain.v)'s
`wp_main_getopt` is the call main makes, with
`libc_getopt_refined_contract (hello_input av sargs) … transition` in
the registry. That is Campaign 4's safety contract with a `transition`
conjoined to each ordinary return's postcondition; its admission,
writes and prefixes are the safety contract's, and `getopt_returned`
reads the safety post through `refined_invoke_base`. The
run's arguments `sargs` are strings in objects of their own, as the
launcher copies them. `hello_input` is getopt's input for the whole
run: argv, "g:t" and Hello's four long options, every flag null. Main
hands over argv the way HelloConv hands mbrtowc its cells: one block
(`block_ps`) of argc + 1 slots. Its bytes are those of the pointers it
holds (`argv_bytes`) and its aux slots their capabilities (`argv_caps`).
- The admission (`getopt_admitted`) reads `getopt_slots` from that block
  and the arguments' lives. Each slot's capability names a live
  argument, so it is not freed and its aux piece holds it exactly.
- The return is framed by `prefix_agrees_out`, whose one block out is
  argv. The new `getopt_slots`, with its byte bounds, turns memory back
  into a block of the same form (`argv_of_slots`). This is where the
  bounds are needed: a slot whose bytes are only known to load as a
  pointer does not fix the bytes the pieces name.
- The triple hands back another permitted order `ps'`, the strings
  unchanged and the token renamed to the new optarg and optind, with
  optind in range. `hello_code` adds that the code is a C int and that
  a 'g', short or `--greeting`, comes with a nonnull borrow of an
  argument.
- The code is a `getopt_step` from the token: some call from a memory
  and world where wi holds with the token's pieces made the transition
  with that return (`getopt_stepped`, by `refined_return`). The loop
  ignores it; the version path below uses it.

The premises on wi are call-local:
- `Hgetopt_wi`: the cells and token are current.
- `Htable`: the literals are in memory.
- `Hgetopt_env`: libc's side of admission.
- `Hgetopt_apart`: roots, cells and releases apart from the program.
- `Kgetopt`: wi survives with the block and the token rewritten.

**The option loop.** `main_loop` is a Löb induction at the entry of
`iw_1.L8`. getopt promises no bound on how often it returns, so the
loop may run forever, which `never_panics` allows. Each round enters a
block, and that step guards the induction hypothesis. The code's
32 bits are compared (`int32_eq`, `int32_end`), and the cases are:
- `'g'`: optarg is loaded through the token (GetoptLogic's
  `wp_optarg_check` and `wp_optarg_load`) and stored in the greeting's
  cell b4, then back round.
- `'t'`: the traditional greeting is stored, then back round.
- Any other code but help and version: back round with pr.2, the
  "lose" flag, set to 1.

The exits are left to continuations (`loop_exit`): `iw_1.L21`
(version), `iw_1.L39` (help) and `iw_1.L10` (end of options). Each
gets the loop's pieces (`loop_res`): argv's block, the strings, the
token, and b4 holding a `greeting_ok` pointer, which is the default,
the traditional greeting, or a nonnull argument borrow. It also gets
pr.2 at 0 or 1. Main owns everything else the start block left
(b4's tail, b6, the lent names and the codec), and the continuations
capture it.

`main_to_loop` composes `main_start` with the loop, through
`main_to_L8`. It takes argv as a block holding the arguments in order
(`argv_block_split` lends its first slot to `main_start`) and the token
at any optind in range. It
needs the launcher to give the arguments' strings objects of their
own, which Startup.v's `copy_slots` does, one allocation per string.

**The operand check.** `main_operands` goes from `iw_1.L10` to three
exits (`operand_exit`), each with a fact about pr.2 and optind:
- `iw_1.L79`, an extra operand: optind < argc.
- `iw_1.L113`, the hint to try --help: pr.2 set and optind = argc.
- `iw_1.join`, on to greet: pr.2 clear and optind = argc.

With pr.2 clear, main compares the token's optind with argc. If an
operand remains, or pr.2 is set, main loads `c: argv[optind]`. The token
keeps optind at most argc, so the load is of one of argv's argc + 1
slots. `argv_block_slot` lends that slot's pointer cell out of argv's
block for `wp_raw_load_pointer_in`, and its capability is an
argument's, whose life main owns, or the sentinel's, which is null.
`operands_exit` makes the operand check the loop's end-of-options exit.

**The version path.** `main_version` is the loop's exit at `iw_1.L21`.
Given the version literals' pieces, main does four things:
- it loads stdout's stream through the world (`wi_stdout`, as in
  HelloVersion's footer);
- it calls `proper_name` four times (`wp_main_proper_name`; the helper
  is the identity);
- it calls `version_etc` through HelloVersion's `version_etc_spec`,
  with that section's premises taken over as main's;
- it calls `exit(0)`.

`exit` has a contract that never returns into main (`wp_main_exit`,
the same shape as HelloClose's `_exit`). In this language the call
stalls. The handlers exit runs, close_stdout among them, are the
ending's, and Campaign 4's Ending and Linked compose them with main.
Since main never resumes, the loop's pieces are dropped there.

**--version from main's entry.** `main_to_version` proves main from its
entry to `exit(0)` by --version alone, where every `getopt_step` from
the first token returns 129. Its premises are those of the start block,
getopt's call and the version block; none of the greeting's, --help's
or the diagnostics'. `main_to_L8` is the start block up to the loop's
first entry, and
`loop_version` is the loop's first round: the call, the comparison with
-1 and the branch by `iw_1.L19` to `iw_1.L21`. The code-129 premise is
where Campaign 4's concrete binding enters. Its transition for argv
`[hello, --version]` with a fresh parser yields 129, and its wi has to
tie the first token to that fresh parser. The safety contract alone
cannot do this: it allows `'?'` for the same input and memory, so
without the transition the other exits are reachable as far as the
contracts say.

**The help path.** `main_help` is the loop's exit at `iw_1.L39`, the
inlined `print_help`. It needs the help literals' pieces, the string
"en_", the program-name cells and LC_MESSAGES' lent name. The steps
are:
1. Load stdout through the world.
2. Query LC_MESSAGES with `setlocale(5, NULL)` (LentLogic's
   `wp_lent_query`). The premises `Hquery_pre` and `Hquery` are
   LocaleLogic's `locale_wi_pre` and `locale_wi_query` for libc's
   world.
3. Load the program's name from its cell. It is a suffix of argv[0]
   (`name_ok`), and its life is among the arguments' pieces.
4. Print the usage line and the six option lines (`wp_help_output`),
   then call the footer through HelloVersion's
   `emit_bug_reporting_address_spec`.
5. Compare the locale's name with "en_". The name is lent, so it is
   never null. The comparison uses the new `wp_strncmp_lent`, whose
   bound comes from `terminated_bounded`. If the name is not English,
   print the translation-bugs line.
6. In `help_L32`, compare stderr with stdout and exit with 1 or 0.

Every output call is admitted for these exact arguments (the
`Hhelp_*` and `Houtput_*` premises) and keeps the whole `wi`, getopt
token included, on success and on failure. Campaign 4's
`libc_stream_frame` preserves locale, errno, shutdown and the other
stream, but not `libc_getopt`. A concrete `wi` therefore has to show
that these calls keep optarg, optind and the parser's state.
Getopt's sampled errno may change, and `getopt_current` does not
constrain it.

**The operand errors.** These two blocks are the operand check's
other exits:
- `main_hint`, at `iw_1.L113`: main prints to stderr that --help says
  more, naming the program (`main_output_args`, now covering stderr's
  line too), and exits with 1.
- `main_extra`, at `iw_1.L79`: main loads argv[optind] again. Since
  optind is below argc, that slot holds an argument (`slot_kinds`).
  Main reports it with `error(0, 0, ...)` and goes on to the hint.
  This `error` owns no errno piece, so its premise `Hdiag_post` keeps
  the ghost heap unchanged and returns with nothing. HelloClose's
  four-argument `error`, in contrast, hands back the errno block it
  owns. A concrete `wi` discharges `Hdiag_post` with Campaign 4's
  returning diagnostic frame, in its no-owned-errno form.

`loop_exits` gathers the loop's exits other than the greeting.
`main_to_join` composes them with `main_to_loop`. Main is then proved
from its entry through every path except `iw_1.join`, which is entered
with pr.2 clear and optind at argc, and is left to one continuation.
The version and help paths use up the literals and the program's
name cells. The greeting needs neither.

**The greeting.** [HelloJoin.v](../rocq/theories/hello_contracts/HelloJoin.v) proves
`iw_1.join` and composes it with the rest. It is a file of its own so
that HelloMain does not wait for HelloConv: the two compile side by
side, and HelloJoin after both. HelloMain takes only HelloConv's pure
part, [HelloConvDefs.v](../rocq/theories/hello_contracts/HelloConvDefs.v).
- `xmalloc_spec`: malloc's contract has no null return, as running out
  of memory is a resource ending. So xmalloc's call of `xalloc_die`,
  and the `abort` behind it, is never reached, and `exit_failure` is
  not needed.
- `greeting_string`: b4's greeting is the default literal, the
  traditional one or a suffix of an argument, a string main owns and
  gets back.
- `main_join`: strlen, xmalloc of 4 × (len + 1) bytes, and
  HelloConv's `rpl_mbsrtowcs_spec`. That spec's postcondition now also
  says the errno block keeps 4 bytes. If the result is -1, main loads
  errno and calls `error(1, errno, ...)`. That is the same contract as
  main's extra-operand diagnostic, since `error` is one function, and
  with status 1 it never returns (`Herror_fatal`). Otherwise main calls
  `wprintf` on the converted string (`Hwprintf_pre` asks for the wide
  characters and their NUL), frees the buffer and calls `exit(0)`.
- `main_full`: `main_to_join` composed with `main_join`, so main is
  proved from its entry through every path. Every path ends in exit,
  in a fatal `error`, or in the option loop running for good.
- `hello_main_safe`: `heap_labelled_safe` from `main_full`. Given an
  initial ghost heap that agrees with memory, satisfies wi and holds
  main's pieces, no labelled run of main fails at any fuel: no panic,
  no stuck step, no contract violation, and so no abort. The audited
  codec premise `Haudit` stays explicit. `Print Assumptions` is
  closed.

HelloJoin's section takes HelloMain's premises and HelloConv's extra
ones as one list. Where the two named the same thing, they are now one
premise. libc's `rep` and `requests` are shared, and setlocale is
`libc_setlocale_contract rep requests` for both files. The query
premises `Hset_query_pre`/`Hset_query` (any lent category, a pointer
with a null address) give HelloMain's LC_MESSAGES-only
`Hquery_pre`/`Hquery`. The theorem is still conditional on the
call-local wi premises; no concrete wi discharges them yet.

## Open questions for mbrock

- Start the logic now, or finish Campaign 4's hi.c first?
- Iris, as recommended after the spikes, or the hand-rolled logic?
- Is "frees nothing live at a safepoint" the premise wanted for every
  single-threaded program, or should Runtime.v gain a single-threaded
  runtime type that has it as an axiom with a native test? Answered
  (2026-11-09): neither. There is no premise. Runtime.v's safepoint
  axiom is the collector's alone, `collector_live` (no region changes
  at a safepoint, native test axiom-collector-live.c), for every
  runtime. A signal handler or a thread is program code, to be
  verified with an invariant that it frees only what it was handed.
- Should the ladder's middle rungs (types, certificates) be designed
  before the spike, or only after it shows what a derivation looks like?

See [meta](concepts/meta.md), [live](concepts/live.md) and
[adequacy](concepts/adequacy.md) for the three new terms.
