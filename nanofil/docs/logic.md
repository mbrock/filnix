# A program logic for never_panics

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
| `buffer_never_panics` | [Buffer.v](../rocq/theories/Buffer.v) | a heap object at any fresh base; `holds_buffer` is `meta b 32 Heap` and `live b` written as one non-separating fact; it once took `safepoint_keeps_live`, the instance premise the proposal asks for, which Runtime.v's `collector_live` now makes a lemma |
| `valid_no_unchecked` | [Soundness.v](../rocq/theories/Soundness.v) | Campaign 3: no run of a valid module that starts ready reaches `unchecked`, over every runtime; stuck past any external call but free |
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

They share [Pieces.v](../rocq/theories/Pieces.v), the resource model:
pieces keyed by [identity](concepts/identity.md) (an object's life,
one byte, one aux slot at an offset), the global fact that live objects
are disjoint, and `safepoint_shape`: a safepoint keeps every region
and every byte, and rewrites only aux slots that hold a freed object's
capability (from `collector_live`, `non_moving` and
`aux_round_trip`). Keying by identity is forced, not
chosen: the model's `fresh` lets a new object take a freed one's
addresses.

| | Hand-rolled ([Sep.v](../rocq/spikes/Sep.v), [SepListSum.v](../rocq/spikes/SepListSum.v)) | Iris 4.5 ([IrisLang.v](../rocq/spikes/IrisLang.v), [IrisHeap.v](../rocq/spikes/IrisHeap.v), [IrisListSum.v](../rocq/spikes/IrisListSum.v)) |
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

The hand-rolled spike stays as the record of the alternative and of
what the logic must prove about Fil-C's memory, which Pieces.v holds
for both. Buffer.v remains the last single-invariant proof; BufferLogic.v
proves the same theorem through the program logic.

## Progress

mbrock chose Iris (November 2026), in the Iris, RustBelt and Cerise
tradition. Steps 1 to 4 above are done, and step 5 is under way:

| Step | Where | Result |
| --- | --- | --- |
| 1, step lemmas | [StepRules.v](../rocq/theories/StepRules.v), on the main build | one forward rule per instruction form and jump; Cycle.v 13 s to 4.4 s, Buffer.v 23 s to 7.4 s, Prefix.v 63 s to 45 s through Symbolic.v's `take_step`. Prefix's remaining time is mostly dropping wraps (`mod 2^64`) from values |
| 2, the language | [Language.v](../rocq/theories/Language.v) | an `ectxi_language` whose context is the callers stack; fuel in the state; a return to a caller is two Iris steps; endings that are neither failures nor returns stall; `wp_never_panics` proves Panics.v's `never_panics` |
| 2, the rules | [Logic.v](../rocq/theories/Logic.v), [Heap.v](../rocq/theories/Heap.v) | the identity-keyed ghost heap (Heap.v) and its state interpretation; one lifting lemma closes safepoints and stalls by Löb; a weakest-precondition rule per instruction (`wp_check`, `wp_raw_load_pointer`, `wp_alloc`, `wp_call_bind`, ...) |
| 2, the list sum | [ListSumLogic.v](../rocq/spikes/ListSumLogic.v) | `sum`'s triple `{{{ lst p xs }}} sum {{{ RET Ret (list_sum xs); lst p xs }}}` hands the list back and states the result; `listsum` uses it through `wp_call_bind`; 14 s, against 38 s for the spike on the old language |
| 3, rendering | dterm-rocq (another thread) | Iris notation and proof-mode states on the site |
| 4, the main build | [_RocqProject](../rocq/_RocqProject), nix/rocq.nix | Pieces.v, Heap.v, Language.v and Logic.v are part of the model, built and parse-checked by the quick gate with stdpp and Iris from the pinned nixpkgs; they add about 13 s of compile time off the critical path. The list-sum examples stay in spikes/ |
| 5, a program in the main build | [BufferLogic.v](../rocq/theories/BufferLogic.v) | `buffer_never_panics` again, through the logic: the allocation's `obj` splits into `live` and four cells, each loop is a Löb induction carrying them, each check lends `live` back for a step and each access takes the one cell it reaches (`cells_at`). Without `live` in the sum loop, or with three cells, the proof fails. Needs no new rule: `buffer` has no named locals and checks only class `a`. 14 s, after `arith` learned to treat a remainder by a constant as a bounded variable before reaching for division equations (`mod_atoms`, `arith_fast` for side goals that may be false): BufferLogic.v 24 s to 18 s to 14 s, Cycle.v 6.3 s to 3.9 s, Buffer.v 10.4 s to 6.6 s, ListSumLogic.v 17.5 s to 13.1 s, Prefix.v unchanged (its time is kernel checking and stepping) |
| 6, contracts | [Language.v](../rocq/theories/Language.v), [Logic.v](../rocq/theories/Logic.v), [ContractFrame.v](../rocq/theories/ContractFrame.v) | the language takes a contract registry and a world: an admissible external call returns through Campaign 4's `invoke`, returns badly (`EBad`, never safe) or stalls (blocking, exit, resources); `adequate_labelled` and `heap_labelled_safe` prove the labelled machine's safety (no `failure_ending`, a return satisfies the postcondition) from a WP; `wp_external` is the call rule; the state interpretation gains a world interpretation `wi`, kept at safepoints (`SafepointStable`). The frame for a call: if a contract's writable roots share no address with the program's live owned objects and it releases none of them, the ghost heap still agrees after the whole effects path (`prefix_agrees`), and roots the call delegates stay apart (`delegates_apart`). Separation is by address, not identity, a premise of the program's theorem rather than of `puts_pre` (Campaign 4 agreed: formal.md promises no blanket input immutability) |
| 6, hi.c | [HiLogic.v](../rocq/theories/HiLogic.v) | `hi_logic_safe` for every runtime and `interp_hi_logic_safe` from Hi.v's fixture, closed. The program owns its literal as a `string`; the world interpretation is `stdio_wi` (puts's rep, `stdio_ready`, the world's roots apart from the program's objects); puts is `wp_puts` from StringLogic.v; main is six tactic lines. No new rule was needed: main has no named locals and no check |
| 7, strings | [StringLogic.v](../rocq/theories/StringLogic.v) | `string p b reg bytes`: the life of the object p's capability names, read-write or read-only, and its bytes through the NUL; owning it gives Campaign 4's `terminated_length` and `c_string` (`string_facts`), lends a suffix (`string_suffix`) or one byte (`string_byte`). Triples derived from the contracts, each stated at any call site: `wp_strlen` and `wp_strchr` (pure calls: memory and world unchanged, `pure_return`) over any registry and world, `wp_puts` under `stdio_wi` (the frame keeps the string through puts's writes). New rules: `wp_check_read`, a read check through an `Obj` or `Ro` capability, and `wp_raw_load_byte`, a one-byte load |
| 7, a read after a call | [ScanLogic.v](../rocq/theories/ScanLogic.v), [scan.c](../rocq/programs/scan.c) | `scan(s)` takes `strlen(s)`, finds the first `l` with `strchr`, prints the rest with `puts`, then reads the byte after the `l` through strchr's pointer: three calls and a read after the last one. `scan_logic_safe` for every runtime and `interp_scan_logic_safe` on Hi.v's fixture ("hello"), closed. The proof (`scan_spec`) is 43 lines: one rule per instruction, the three triples, and the facts that make the read safe: strchr's hit is before the NUL because `l` is not 0, so the byte after it is in the string the frame kept through puts. Still no named locals, so `wp_ret` needed nothing new |
| 7, a helper in a loop | [CountLogic.v](../rocq/theories/CountLogic.v), [count.c](../rocq/programs/count.c) | `next_l` is strchr for `l`, with its own triple (`next_l_spec`, 13 lines, from `wp_strchr`); `count_l` calls it once and then in a loop on the suffix past each hit, reading the byte each hit lands on. Both calls use the triple through `wp_call_bind`; the loop is a Löb induction at the head (`count_loop`, 46 lines) carrying the string and "the pointer is null or before the NUL" (`found_from`), re-established from the callee's postcondition on the suffix (`found_next`). `count_logic_safe` and `interp_count_logic_safe` (two `l`s in "hello"), closed; 5.3 s. No new rule: no named locals, so `wp_ret` is still the one without them. `gen_env` moved to Symbolic.v for both loop proofs |
| 7, writes, malloc and free | [MemLogic.v](../rocq/theories/MemLogic.v), [Logic.v](../rocq/theories/Logic.v), [Heap.v](../rocq/theories/Heap.v) | a block of memory is owned piece by piece: `bytes b o xs` and `auxes b o cs`, its bytes and its aux slots. `wp_memset` from `memset_contract`: the block's bytes become c's low byte and every slot starting in it is emptied (`clear_slots`). `wp_memcpy` from `memcpy_contract`: a destination block and a source block in another object, both 8-aligned and so in phase; the destination takes the source's bytes, each full slot takes the source's capability and a partial one empties (`copy_slots`, `copy_after`); the source comes back unchanged. The contracts' exact destination frame keeps every other piece (`block_frame`, through Heap.v's `frame_within` for writes inside one live object). Blocks start at a multiple of 8, so the slots a write touches start inside them. `wp_strdup` from `strdup_contract`: owning a `string`, the call returns a fresh object owning a copy as a `string` (its other bytes and its slots unowned); its writes lie in the fresh object, so `frame_other` keeps the rest. `wp_malloc` from `malloc_contract`: the fresh object's pieces (`obj`), no null case, since the selected malloc refuses with a resource ending. Logic.v's `wp_free` gives up a heap object's `live`, whose ghost token ends as `VFreed` (the ghost heap cannot delete a key), and `wp_free_null`; both take `frees_heap` of the genv's free, which Runtime.v does not promise (it proves only what a free may change) and `frees_heap_interp` proves of `free_res`. `wp_raw_store_byte` is new for a one-byte store |
| 7, a callee owning memory | [SlotLogic.v](../rocq/theories/SlotLogic.v), [slot.c](../rocq/programs/slot.c) | `fill(c, n)` keeps one heap buffer in its static `slot`, with its size in `slot_size`: if n does not fit it frees the buffer and mallocs n + 1 bytes, then memsets n bytes, writes the NUL and returns the buffer. The module invariant `slot_inv` owns both statics and the `buffer` they describe (null and 0, or a live heap object with all its bytes and slots). `fill_spec` takes the invariant and returns `lent`: the n filled bytes and a wand that, given them back, returns the invariant, so the caller cannot keep them across its next call. `use` calls `fill` three times (grow, reuse, grow) and reads the buffer after each. `slot_logic_safe` for every runtime whose free `frees_heap`, `interp_slot_logic_safe` from the module's initial memory, closed; 14.8 s. Still no named locals: nanofil keeps `fill`'s and `use`'s locals in temporaries |

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
| shared, written once | none | from MemLogic.v: blocks as pieces (60), the frame and memset's effect on them (`block_frame`, `fill_after`, 90), `wp_memset` 63, `wp_malloc` 50; `wp_free` and `wp_raw_store_byte` in Logic.v. MemLogic.v also has `wp_memcpy` and `wp_strdup`, which slot.c does not use |
| compile time | well above a second per call site | SlotLogic.v 14.8 s (`fill`'s two lemmas about 4 s each, `use_spec` 3.5 s), MemLogic.v 3.2 s for memset and malloc, 5.1 s with memcpy and strdup |
| conclusion | every stop named | no stop is a `failure_ending`, a return is an int |

The invariant is what the hand method lacks: the state `fill` leaves for
its next call is a separation-logic assertion, so the second call needs
nothing about the first beyond `slot_inv`, and the caller's reads are
safe because it holds the bytes the triple lent. The wand in `lent` is
quotearg's contract with its caller: the buffer is valid until the next
call. Writing it needed one fact Runtime.v does not state, that free
succeeds on a live heap base and on null (`frees_heap`); it is a premise
of `slot_logic_safe`, proved for the interpreter's runtime, and could
become an axiom of Runtime.v after review.

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
| `free` | consumes `live b` | that it frees only its argument's object. Done (`wp_free`), with `frees_heap` a premise |
| quotearg | a slot invariant, with the result lent: `string ret ∗ (string ret −∗ slots)` | that a buffer it returns is valid only until the next call with the same slot that grows it. Shown on slot.c (`slot_inv`, `lent`) |
| exit, atexit | the registered functions' specs, by case on the pinned targets | the order and set of callbacks (Campaign 4's registry) |
| every call | the frame rule | the writable roots and nothing beyond them: no write, free or capability change outside the footprint |

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
