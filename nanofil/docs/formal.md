# The formal campaign: checked IR, certificates, and Rocq

November 2026. This extends [campaign.md](campaign.md), which states
nanofil's foundation; read that first. The campaign below is a plan,
and each campaign ends with a note in `docs/` that says what it found;
the table below says what is built.

Routine pushes prioritize iteration: the relevant Rocq gate builds the
model, runs parse.sh and compares base verdicts on a small corpus without
mutations. The full multi-mode mutation matrix is deliberate evidence
for a release or soundness-relevant change, not the cost of every edit.
Unrelated web/docs changes skip Rocq. See [rocq.md](rocq.md) for the quick
and full commands, budgets and what each does and does not establish.

## The ambition

nanofil becomes a Fil-C whose safety checks are removed exactly where a
machine-checked proof says they cannot fire, with no annotations in the
C, no new language, and no trust in the analysis that proposed the
removal. The checked IR already states every Fil-C obligation as a term
and already has an executable semantics ([interp.pl](../src/interp.pl));
the campaign gives that semantics a second, foundational home in Rocq,
states the runtime's promises as axioms, and turns the validator's
hand-blessed evidence shapes into an open-ended certificate language.

The reason this is tractable now is a property of Fil-C itself: a trap
is terminal and uncatchable, so a `check(Lo, Hi, Rights, Align)` is a
pure assertion. An assertion that cannot fail is dead code, and deleting
it preserves behavior exactly. The whole program never needs proving:
runtime checks at a boundary establish preconditions (`span_test(Lo, Hi)`
and `limit` already do this), and proofs carry them through the hot code.

Two properties run through this page and must not be confused:

- **Soundness of checking** (`valid_no_unchecked`, Campaign 3): every
  run of every valid checked module avoids `unchecked`. It is a theorem
  about the validator, for all valid modules at once: the checks it
  demands, and the checks it lets a pass remove or reuse, are enough, so
  a check that fails is the run's whole story. It does not say that a
  check never fails; programs with memory errors are valid and panic.
- **Trap-freedom of a program, "it never panics"**: no Fil-C check of
  one particular program, as compiled and linked, ever fails. That is
  memory safety with respect to Fil-C's capability semantics, a
  per-program theorem with no general version, ideally of a whole pinned
  Nix closure; it builds on the first ("Campaign 7: a program that
  never panics", below).

Three things fall out of a well-stated model beyond nanofil: a
definition of Fil-C independent of LLVM, which does not exist today; a
trusted base small enough to hand to the runtime's author as one page of
axioms; and, at the horizon, translation validation of filcc's own
output through the same checker, which is how the work would reach every
package in Filnix rather than only what nanofil compiles.

## The campaigns at a glance

| Campaign | Goal | Deliverable | State |
| --- | --- | --- | --- |
| 0 | Measure which checks survive `-O --checks=combined` | [docs/residual.md](residual.md) | measured: 10,353 Lua data-check sites, 24.49% flag-only renewals; cycle costs estimated from native benchmark calibration; spatial-certificate pilot before ownership |
| 1 | The core model in Rocq, agreeing with the interpreter | Gallina syntax, semantics, `valid` | under way: syntax, memory and small-step semantics in `nanofil/rocq/`, agreeing with `interp:run/5` on every core-subset run line, and `valid` for functions, data and aliases, agreeing with `ir:valid_module/1` on every core-subset mutant of the corpus and of tests/gen.pl's Fil-C modules, both under every `--checks` mode with and without `-O`, and of the tests/c/prog programs with aliases and weak, thread-local or constructor data; floats (`Ieee.v`) and variadics are in the subset, so every corpus run line is compared and all of Lua 5.4.7's functions but `luaD_rawrunprotected` (`setjmp`) decode into it, with Lua's state-free functions run by the gate ([rocq.md](rocq.md)); tests/gen.pl's Fil-C modules now reach `renew_if`, `limit` with `check_limit`, and `renew_hull`, with frees and traps; found and fixed: a renew of a freed variadic snapshot was `unchecked(span)`, now a trap as native renew gives; dominance now transcribes cfg.pl's `cfg_idoms/2` and `dom_intervals/3`, so the validator judges Lua's lvm.c; the model's runtime is Campaign 2's module type; the three data findings are decided (data items have the header's shapes, a call of data traps, names are unique) |
| 2 | The runtime as one page of axioms, each probed natively | `docs/runtime-axioms.md` | first version: [runtime-axioms.md](runtime-axioms.md) and `Module Type Runtime` in `nanofil/rocq/theories/Runtime.v`, ten axioms read against staging `18b6663`, each with a native test in tests/c/prog/axiom-*.c (the eighth, `address_space`, from Campaign 3's coverage lemma; the ninth and tenth, `free_keeps_ids` and `free_checked`, from Campaign 3's theorem); the interpreter's instance proves them all, and three readiness obligations without a native test (the third, `freed_bounds`, from Campaign 3's half check); Campaign 3's machine runs over any instance; since 2026-11 the safepoint axiom is the collector's alone, `collector_live` (no region changes at a safepoint; test axiom-collector-live.c), with `safepoint_lifetime` and `rooting` lemmas from it, because a handler or thread that frees is the program's code |
| 3 | Soundness of checking: the validator's theorem | `valid_no_unchecked`, no admits | started: [Machine.v](../rocq/theories/Machine.v) runs the steps over any `Runtime` and proves `ready` an invariant of every run, and every step a `step_rel` step or a safepoint action; [Coverage.v](../rocq/theories/Coverage.v) proves the coverage lemma, given `objects_fit` (its proof needs only objects ending at or below 2^64; the axiom says 2^48, native's bound, which `hull_covered` needs: mbrock's decision); the interpreter broke that (`rocq/tests/huge-object.ir`, a valid module run unchecked), and now traps where native Fil-C refuses an allocation, with the runtime axiom `address_space` supplying the hypothesis in every state of a run that starts ready; a valid module's initial data has no size limit, so the theorem takes "the run starts ready" as a hypothesis (mbrock's decision; starting the heap above the data is the planned fix); [Evidence.v](../rocq/theories/Evidence.v) proves the evidence pass sound instruction by instruction and across an edge; [Persistence.v](../rocq/theories/Persistence.v) carries it over whole runs: in every state of a run, a frame that is not doomed runs no raw access or raw call to `unchecked` except by `hull_covered`, using that the runtime changes no region at a safepoint the pass keeps facts across (`spares`; the pass keeps facts across three such; once a hypothesis, now a lemma for every runtime, `spares_any` from `collector_live`); [Dominance.v](../rocq/theories/Dominance.v) proves the validator's dominator intervals sound for every function (a run enters only blocks with an interval, and dominance holds across each edge), which the reuse forms' single-definition chains rest on; [Interval.v](../rocq/theories/Interval.v) proves the offset intervals `offset_interval/8` answers sound, wherever the names they walk hold their definitions; [Sites.v](../rocq/theories/Sites.v) proves that a single definition's operands are not defined again where it dominates; [Identity.v](../rocq/theories/Identity.v) proves that no run loses an object, since the runtime's free keeps identities (the axiom `free_keeps_ids`, first a hypothesis), so a check that passed passes again or traps; [Single.v](../rocq/theories/Single.v) proves that in every frame of every run each single definition whose site dominates the point replays, its operands unchanged and its memory persisting; [Chain.v](../rocq/theories/Chain.v) reads guard chains and pointer distances off it and proves the first reuse form: along every run, an access `hull_covered` accepts gives no `unchecked` (`interp_access_checked`, closed), with the evidence invariant now carrying that the live facts' pointers dominate the point (Dominance.v's `dom_meet`, from the nearest-common-ancestor property of `cfg_idoms/2`); [Renew.v](../rocq/theories/Renew.v) proves the next three: along every run, no renew, renew over a hull or half check the pass accepts gives `unchecked` (`interp_reuse_checked`, closed), with `address_space` now saying objects start at or above 0 and a readiness obligation that freed objects are empty (`freed_bounds`); [Guard.v](../rocq/theories/Guard.v) proves `renew_if` and `check_limit` the same way (`interp_guard_checked`, closed), with no new hypothesis; planning `check_ahead`'s doomed frame found a valid module the interpreter ran to `unchecked(ahead)`, a check whose start wrapped onto the need's end modulo 2^64, now refused (`near_offset/1` of K + Lo in `ahead_insts/8` and the pass, [rocq.md](rocq.md), "A need past 2^64"); [Ahead.v](../rocq/theories/Ahead.v) reads the pass's needs back as facts at each point and proves its one sweep computes them; [Doomed.v](../rocq/theories/Doomed.v) proves that along every run a frame a `check_ahead` doomed never steps to `unchecked` (`interp_doomed_checked`, closed), carrying the validator's need as facts at the frame's point; [Soundness.v](../rocq/theories/Soundness.v) assembles `valid_no_unchecked`: along every run of a checked module that starts ready, no step is `unchecked` (`interp_valid_no_unchecked`, closed, a plain instance), with no runtime hypothesis beyond the ready start (`spares` was one while the safepoint stood for signal handlers too, mbrock's decision; since 2026-11-09 every runtime meets it by `spares_any` and the statements drop it; a handler a program installs could still free a checked object at a pointer store's aux exit, a constraint on verifying handlers), the axioms `free_keeps_ids` and `free_checked` (each with a native test), and external calls other than `free` stuck until Campaign 4's contracts |
| 4 | Observations, refinement, and libc contracts | a trace semantics; `opt:refines/2` as trace inclusion | [ExternalCalls.v](../rocq/theories/ExternalCalls.v) states trusted contracts and finite effect prefixes, starting with `puts`; [ExternalMachine.v](../rocq/theories/ExternalMachine.v) adds guarded direct-call transitions and finite labelled runs, preserving readiness, identities and Campaign 3's two invariants; native instances/trace coverage, executable integration and refinement remain open |
| 5 | Static discharge by certificate | `discharged(Cert)`, `discharge_ok`, a Prolog finder | not started |
| 6 | Integration with Filnix and the playground | the `nanofil-check` gate | not started |
| 7 | Trap-freedom of a pinned Nix closure: a program that never panics | `never_panics` of one closure: a closed module, then a one-call libc program, then GNU Hello (`nanofil-hello-O`); `ls` next; this build of OpenSSH's server as the stretch | [step 0 measured](trap-census.md): Hello has 1,398 class-`a` sites, 360 flag-only renewals; all 178 functions in 81 objects inside the subset, `valid = Some true`; `never_panics` stated in [Panics.v](../rocq/theories/Panics.v); step 1 proved for every runtime: [Sum.v](../rocq/theories/Sum.v)'s `sum_never_panics`, a closed loop over a global array, and [Prefix.v](../rocq/theories/Prefix.v)'s `prefix_never_panics`, the same loop bounded by an `int` input, for every input; [Cycle.v](../rocq/theories/Cycle.v)'s `cycle_never_panics`, a loop the input runs up to 2^31 - 1 times, by assertions at each point (Floyd's method) instead of enumerated runs; [Buffer.v](../rocq/theories/Buffer.v)'s `buffer_never_panics`, the same over a heap buffer at any base the allocation returns; the Iris program logic is in the model ([Logic.v](../rocq/theories/Logic.v), [logic.md](logic.md)), with the list sum's triple as its first example and `buffer` proved through it in the main build ([BufferLogic.v](../rocq/theories/BufferLogic.v)); hi.c's body through it with puts's contract ([HiLogic.v](../rocq/theories/HiLogic.v)), compared with Hi.v's hand proof in [logic.md](logic.md); `scan`, which reads memory after strlen, strchr and puts, through triples derived from Campaign 4's string contracts ([StringLogic.v](../rocq/theories/StringLogic.v), [ScanLogic.v](../rocq/theories/ScanLogic.v)); `count_l`, a loop calling a helper through the helper's own triple ([CountLogic.v](../rocq/theories/CountLogic.v)) |

## The claims, kept apart

[campaign.md](campaign.md) already separates three claims; the formal
work keeps that separation, attacks them in this order, and adds a
fourth, about one program rather than about nanofil.

| Claim | Statement | Status today | This campaign |
| --- | --- | --- | --- |
| Soundness of checking ([campaign.md](campaign.md)'s checked-IR safety) | Every execution of a validated checked module, under the runtime axioms and environment contracts, avoids `unchecked(Reason)`; its traps are the whole story | `ir:valid_module/1` in Prolog, differential tests, bounded symbolic search | The central theorem, machine-checked (Campaign 3) |
| Transformation correctness | A pass's output refines its input's observations | `opt:refines/2`, ad hoc; `check_reuse:reuse_refines/2` and its kin per check pass | A trace semantics and refinement relation (Campaign 4); certificates for static discharge (Campaign 5) |
| Implementation correctness | Native lowering and the runtime realize the IR semantics | `amd64_regs_check.pl`, native difftests, snapshot gates | Out of scope for proof; strengthened by a native trace oracle only |
| Trap-freedom of a program ("never panics") | No Fil-C check of one pinned program ever fails, on any input its entry contract allows | nothing beyond tests: a test that passes shows one run did not panic | Per program, on the first three claims (Campaign 7) |

The first claim is quantified over programs and says nothing about
whether any of them panics: a module that reads past an array is valid
and traps, and soundness of checking says only that it traps rather
than running on unchecked. The fourth is the converse question asked of
one program, and is false of many valid ones.

In scope: filc mode, the checked stage, the integer and pointer classes,
`check`, the `raw_*` accesses, `flight`, `poll`, `call` and `free`, and
the reuse vocabulary: `renew`,
`renew_hull(Lo, Hi, Rights, Align)`,
`half_check(Bound, Lo, Hi, Rights, Align)`, `span_test(Lo, Hi)` with
`renew_if(Lo, Hi, Rights, Align)`, `limit` with
`check_limit(Lo, Hi, Rights, Align)`, and
`check_ahead(Lo, Hi, Rights, Align, AHi)`. Since added: the float
classes `s`, `d` and `x`, with [ieee.pl](../src/ieee.pl) transcribed as
Ieee.v, and variadic functions (`va_args`, `va_arg`). Deferred: vectors,
`cas` and atomics, `setjmp` (already excluded from every reuse rule),
`asm_fixed`, plain mode.

The theorem is always relative. Its hypotheses are the runtime axioms
(Campaign 2) and the libc contracts (Campaign 4), and every certificate
names which it relies on.

## Architecture

Prolog stays the producer and the search engine; Rocq becomes the
checker; the build trusts only the checker. nanofil keeps emitting
checked IR and keeps its own validator as a self-check, but a module is
accepted because an extracted Rocq checker replays its certificate, not
because Prolog said yes.

```diagram
 C source, compiled by nanofil
    │  pizlonate and check_reuse          every check explicit, evidence reused
    ▼
 checked IR   discharged(Cert) where a certificate exists
    │  the finder, Prolog and CLP(Z)      proposes invariants; untrusted
    ▼
 certificate   invariant, runtime fact, pinned versions
    │  discharge_ok, extracted from Rocq  replays it; the only gate
    ▼
 accepted module ── nanofil-check ──▶ Nix build
```

Evidence flows down; trust flows the other way, from the model:

```diagram
Evidence: oracle ─▶ certificate ─▶ extracted checker ─▶ build
Trust: runtime axioms ─▶ Rocq model ─▶ soundness theorem ─▶ extracted checker
```

The oracle proposes invariants and hunts counterexamples but is never
trusted; the model is proved sound once against the axioms, and the
checker is its executable shadow. A nanofil bug can produce a bad
certificate; it cannot produce an accepted one.

The division of labour follows each tool's strength: CLP(Z) and
Prolog's relational interpreter are good at search (run the semantics
backwards, find the input that traps, find the interval invariant), and
Rocq is good at never being wrong about a closed term. The certificate
is the contract between them, and it must be deterministic to replay:
theorem, assumptions, program, semantics and checker version all
identified, as [campaign.md](campaign.md) already requires.

## Campaign 0: measure the residual

Goal: a histogram of the checks that survive `-O --checks=combined`
over the Lua corpus, classified by shape, so the roadmap is set by data
rather than taste.

The classification is one Prolog query over checked IR, using the
provenance records ([provenance.pl](../src/provenance.pl)) to reach back
to the C. Shapes worth counting:

- an affine loop index over an array whose length is a visible parameter
  or a `span_test`
- a pointer-chasing load (the pointer came from `raw_load_pointer`)
- a pointer through a phi with mixed origins
- the first access after a call or poll, where only the free flag is at
  stake
- an access through a local or global whose bounds are static
- `itop` and laundered pointers

Two numbers decide the next campaigns. If most surviving checks are
post-safepoint temporal checks, the spatial certificate work
(Campaign 5) buys little and the ownership story (Inquiries) moves up.
If most are affine loop bounds, Campaign 5 pays immediately and the
ordering below stands. Either way, record the cycle cost of each class
on the native benchmarks ([perf.md](perf.md)), since a check that costs
nothing is not worth a proof.

Deliverable: `docs/residual.md` with the table, the query that produced
it, and a one-line decision.

## Campaign 1: the core model in Rocq

Goal: a Rocq development that transcribes [ir.pl](../src/ir.pl) and
[interp.pl](../src/interp.pl) for the core subset, executes by
extraction, and agrees with the Prolog interpreter on the Lua test
suite.

The model is a transcription, not a design: the interpreter already made
the choices. What went over, and from where; the last column links each
definition to its page in [the model](../rocq/theories/Values.v), drawn
by dterm-rocq:

| Rocq definition | Source | Notes | In the model |
| --- | --- | --- | --- |
| `cap := CNone \| Obj base \| Ro base \| Fn f \| External n` | `cap_access_res/7`: `none`, `obj(Base)`, `ro(Base)`, `fn(F)`, `ext(N)` | identity, never bounds | [cap](../rocq/theories/Values.v#cap) |
| `ptr := { ptr_addr : Z; ptr_cap : cap }` | `ptr(Addr, Cap)` | the indivisible flight pair | [ptr](../rocq/theories/Values.v#ptr) |
| `region := { r_base; r_end; r_kind; r_life }` | `region(Base, End, Kind, Life)` | bounds live here, looked up by identity | [region](../rocq/theories/Memory.v#region) |
| `mem := { m_bytes; m_regions; m_aux }` | `mem(Bytes, Regions, Next, Aux)` | aux maps slot address to stored capability; Next became the freshness condition `fresh` | [mem](../rocq/theories/Memory.v#mem), [fresh](../rocq/theories/Memory.v#fresh) |
| IEEE arithmetic on bit patterns | ieee.pl | exact rationals, one rounding function; x87's NaN rule for `x` | [round_ratio](../rocq/theories/Ieee.v#round_ratio), [ieee_binary](../rocq/theories/Ieee.v#ieee_binary) |
| `cap_access_res`, `access_res` | `cap_access_res/7` | the trap reasons in the backend's order | [cap_access_res](../rocq/theories/Memory.v#cap_access_res), [access_res](../rocq/theories/Memory.v#access_res) |
| syntax: func, block, inst, value, module | ir.pl's header tables | core subset only; one constructor per IR functor | [inst](../rocq/theories/Syntax.v#inst), [func](../rocq/theories/Syntax.v#func), [module](../rocq/theories/Syntax.v#module) |
| small-step `step : genv -> config -> step_result`, and `step_rel` | `interp:run/5` | fuel-indexed; `step_rel` takes any fresh base where `step` asks for one | [config](../rocq/theories/Semantics.v#config), [step](../rocq/theories/Semantics.v#step), [step_rel](../rocq/theories/Semantics.v#step_rel) |
| `valid : module -> option bool` | `ir:valid_module/1` | computable, reflection-ready; mirrors the coverage and evidence rules, data and aliases; `None` when a function is outside the subset | [valid](../rocq/theories/Validate.v#valid), [valid_func](../rocq/theories/Validate.v#valid_func), [valid_data](../rocq/theories/Validate.v#valid_data), [valid_alias](../rocq/theories/Validate.v#valid_alias) |

The [outcomes](../rocq/theories/Semantics.v#outcome) are the
interpreter's: `Ret x`, `Trap why`, `UB why`, `Unchecked why` and
`OutOfFuel` for `ret(V)`, `trap(Reason)`, `ub(Reason)`,
`unchecked(Reason)` and `out_of_fuel`. [rocq.md](rocq.md) records the
decisions below as they were made.

Design decisions to make early and write down:

- **Small-step with an explicit configuration, not interaction trees.**
  ITrees buy compositionality the core subset does not need yet, and
  cost coinduction everywhere. Revisit when libc contracts arrive
  (Campaign 4).
- **Values are a sum type over classes.** Well-classedness is a boolean
  check, not a dependent index. Intrinsic typing of `a` and `f` is an
  inquiry, not the baseline.
- **Allocation returns a nondeterministically chosen fresh base**
  disjoint from every region, live or freed. The interpreter's monotone
  Next is one instance; proofs may not rely on it.
- **Externals.** A call to a symbol the module does not define is stuck
  until Campaign 4 gives it a contract.

The decisions as taken, and what each milestone found, are in
[rocq.md](rocq.md).

Gates: the extracted interpreter and `interp:run/5` agree on every test
input and every corpus function (same outcome, same return value, same
trap reason); `valid` and `ir:valid_module/1` agree on every module in
the snapshot corpus, with and without `-O` and under every `--checks`
mode. Disagreement is a finding, not a failure, and gets a fixture.

The places where the Prolog relies on cut order or ground-term
assumptions have no direct Gallina counterpart; each is transcribed
deliberately and recorded in [rocq.md](rocq.md).

## Campaign 2: the runtime as axioms

Goal: one page of axioms, stated at the runtime's interface and pinned
to a Fil-C commit, that the whole development is parametric in, with a
native test probing each one.

In Rocq this is a `Module Type Runtime` (or a section of hypotheses)
that Campaign 1's semantics is written against. The interpreter is one
instance; a test instance for extraction is another; a verified runtime,
should one ever exist, would be a third. The page is also the artifact
to hand to the runtime's author with the question "is this what FUGC
promises?"

| Axiom | Statement | Native test that probes it |
| --- | --- | --- |
| Fresh allocation | `alloc` yields an object disjoint from every live object; its base is fresh as an identity, its address otherwise unknown | reuse an address after a GC cycle; the old capability must still trap |
| Non-moving | an object's address is stable for its lifetime | pointer-to-integer snapshots across many collections |
| Lifetime lemma | bounds change only at `free`, which sets `upper = lower` and the free flag; nothing else touches the header | every reuse rule depends on this; probe with free through an alias between check and access |
| Safepoints | this thread's frees, signal handlers and collector handshakes happen only at calls, polls, alloc, setjmp, `va_arg`, getters and pointer-store ensure-aux | a signal handler that frees, delivered inside a straight-line checked region |
| Retention under concurrent free | memory is not reclaimed while a rooted flight pointer references the object | another thread frees mid-loop; the loop must read retained bytes or trap, never garbage |
| Aux round-trip | a pointer store records its capability; a pointer load returns it, or the freed singleton the collector rewrote it to | store, free, collect, load: the loaded capability must trap |
| Rooting | values in declared frame slots are seen by the collector | the backend's responsibility; probed by the existing GC stress tests |

The failure mode to design against is an axiom slightly stronger than
the runtime's guarantee: assuming no free between a check and its access
(false under threads), or that distinct objects never share an address
over time (false natively). Each axiom therefore gets a test that would
fail if the axiom were strengthened in the obvious wrong way, and the
tests run in the native suite, not the interpreter. [lifetime.md](lifetime.md)
already states most of these as the reasons for today's reuse rules.

Deliverable: `docs/runtime-axioms.md` mirroring the Rocq module type
line for line, with the Fil-C commit it was read against. Revisit
whenever Filnix bumps Fil-C.

## Campaign 3: the soundness theorem

Goal:
`Theorem valid_no_unchecked : forall m, valid m = true -> forall exec, reachable m exec -> outcome exec <> Unchecked _`,
for runs that start ready (the runtime's start state is `ready` for the
module's initial memory, an explicit hypothesis; [rocq.md](rocq.md),
"An object past 2^64"), under the Campaign 2 axioms, for the core subset and every reuse rule in
scope.

This is the theorem [campaign.md](campaign.md) names as "checked-IR
safety", and this page as soundness of checking. It is not the claim
that a program never panics: `Trap(Reason)` outcomes are allowed, and are
what a valid module with a memory error does. What it gives that claim
is that the traps are the whole story, so a proof that a program never
panics reasons about its checks alone (Campaign 7).

It is about the validator, not about any program, and it is where all
the content lives: pizlonation soundness is then the trivial fact that
`pizlonate:pizlonate_module/2` emits valid modules.

Proof plan, in the order the dependencies run:

- **Coverage lemma.** A `raw_load` or `raw_store` whose address operand
  is a check that passed, with Lo ≤ Off, Off + Size ≤ Hi, alignment and
  rights as the validator requires, does not produce `unchecked(Reason)`.
  Pure arithmetic over `cap_access_res/7`. Proved in
  [Coverage.v](../rocq/theories/Coverage.v), given `objects_fit`, every
  object ending at or below 2^48 (its proof needs only 2^64; the reuse
  forms' hulls need the rest), which the runtime axiom `address_space`
  promises in
  every state of a run that starts ready, which the theorem assumes
  ([rocq.md](rocq.md), "An object past 2^64").
- **Proof persistence.** Between a check and a raw use with only
  `evidence_preserving/1` instructions and unpolled edges on every path,
  no free occurred, so the capability still permits the same range.
  Needs the safepoint and lifetime axioms and an induction over the
  paths the validator inspects.
  Proved per instruction and per edge in
  [Evidence.v](../rocq/theories/Evidence.v), and over runs in
  [Persistence.v](../rocq/theories/Persistence.v); where the runtime
  acts was a hypothesis there until every runtime was shown to meet it
  ([rocq.md](rocq.md), "The evidence invariant over runs").
- **Each reuse rule as a corollary.** `renew` (bounds persist, flags
  retested), `renew_hull(Lo, Hi, Rights, Align)` (interval hull),
  `half_check(Bound, Lo, Hi, Rights, Align)` (one bound persists),
  `renew_if(Lo, Hi, Rights, Align)` after `span_test(Lo, Hi)` (guard
  arithmetic through flight chains), `check_limit(Lo, Hi, Rights, Align)`
  (snapshot stability), `check_ahead(Lo, Hi, Rights, Align, AHi)` (every
  path reaches an access that needs the bytes first). Each has the side
  conditions ir.pl already states (single definitions, constant distance
  through one base, no setjmp) and those become the lemma's hypotheses
  verbatim.
- **Assembly.** Progress plus preservation over the step relation, with
  the validator's facts as the invariant.

What the proof will probably find: at least one side condition in ir.pl
that is stronger or weaker than the lemma needs. Both are findings: a
weaker one is a soundness bug with a fixture, a stronger one is a check
the validator could accept and currently refuses.

Gates: the theorem closes for the core subset with no admits; every
reuse rule either has its corollary or is marked out of scope in the
validator transcription (and `valid` rejects it). The invariant for
proof persistence is stated first, since every reuse rule's corollary
rests on it.

## Campaign 4: observations, refinement, and the environment

Goal: one definition of what a program's behavior is, so that pass
correctness, "may trap earlier", and libc contracts are all stated
against the same thing.

Today `opt:refines/2` compares outcomes with special cases, and
[campaign.md](campaign.md) admits it is not a general relation. The
replacement is CompCert's shape: a behavior is a trace of external
events (calls out of the module with their arguments and the bytes they
read, plus the bytes they wrote back) ending in termination with a
value, divergence, a trap with its reason, or `Unchecked`. Refinement is
then trace inclusion with the usual allowance for the original's
undefined behavior.

Three things become precise at once:

- **Trap timing.** "Trap earlier" (`check_ahead`, filcc's scheduler,
  [schedule.md](schedule.md)) means: same trace prefix, then a trap
  instead of the next event. The question of whether a store before a
  crash is observable gets one answer: it is observable only if an
  external call reads it before the trap.
- **Pass correctness.** Each middle-end pass and each `--checks` mode
  gets a refinement obligation. Most will stay tested by difftest rather
  than proved; the point is that the test and any later proof check the
  same relation.
- **Environment contracts.** An external call is an event with a
  contract: the capability authority it requires on its arguments,
  the memory it may write, the objects it may allocate or free.
  A failed premise is a caller obligation that has not been met, not
  a blanket promise that native libc traps: some C violations are UB,
  and each justified trap needs its own failing check.
  `read(Fd, Buf, N)` requires write on [Buf, Buf + N), writes at most N
  bytes there, frees nothing. `malloc` mints a fresh region. `memcpy`
  needs read on one range and write on another. `free` is what the
  interpreter already does.

The contract table is the trusted base for everything about libc
(mbrock's decision: libc stays behind these contracts). The starting
set is [libc-contracts.md](libc-contracts.md): `puts` for `hi.c`, then
the 56 Hello names and `fcntl`, with nine native probes. This trust
also covers the named launcher/libc-TLS entry and host-completion
contracts, with their entry/exit probes (milestone 4i below). Rocq states
these specifications as relations, not global axioms or a purported
proof of libc. The first relation is standalone; Prolog execution and
the extracted driver still model only `free`.

Fil-C's own layering helps: libc is pizlonated C, the runtime's syscall
wrappers check buffer capabilities before the kernel sees raw addresses,
so "the kernel writes only within ranges the wrapper checked" is an
axiom about the wrapper, which is the lowest any userland proof can
reach. Compiling libc with nanofil itself would move libc inside the
theorem and leave only the wrappers axiomatic; that is a Filnix-scale
campaign and is listed under inquiries, not scheduled.

Gates: `opt:refines/2` restated as trace inclusion and difftest passing
under it with no special cases; the oracle runs every Lua test that
calls libc; each contract has a native test that would fail if its
footprint were too small. The contract table grows one function at a
time, driven by the calls the corpus makes.

### Campaign 4, milestone 1: a standalone contract boundary

[ExternalCalls.v](../rocq/theories/ExternalCalls.v) is independent of
Campaign 3's ongoing reuse proofs. `Semantics.v`, `Machine.v`, their
constructors and all existing theorem statements are unchanged.
It supplies these pieces, without claiming the program is closed yet:

- `contract` separates the declared return shape, ABI, caller premises,
  designated capability sources, writable roots, owned releases,
  possible allocation requests, finite observations and normal/resource
  endings. Its panic set describes out-of-contract checks, not an
  executable rule from the negation of the precondition.
- `local_effect` frames bytes and auxiliary metadata outside the
  permitted roots. Changed stored capabilities must be copied from a
  designated source, loaded through a checked complete pointer slot,
  or minted by this call's allocation. A raw address cannot upgrade
  `Ro` to `Obj`. Release permission is distinct from write permission;
  no local/global can be freed by this boundary. Partial pointer-copy
  smidgens need a later extension, not silent havoc permission.
- `ExternalCalls R.effects` alternates these segments with actual
  successful `R.alloc` calls, retaining their exact base and runtime
  state. The call's fresh-object list grows monotonically; old
  identities are never dropped. `effects_preserve`, `prefix_preserve`
  and `invoke_preserve` prove readiness and `persists` from initial
  readiness, using the existing runtime obligations. There is no new
  runtime axiom and no assumption about `R.free` preserving identities:
  releases are constrained directly by the relation.
- `prefix` does not depend on eventual completion. `invoke` retains its
  last internal memory/runtime snapshot even for a resource ending;
  `invoke_prefix` exposes that prefix. Allocation refusal needs a
  contract-authorized request with `R.alloc = None`; `TooBig` needs an
  authorized original byte count exceeding the existing size limit,
  before `heap_req` rounds the extent. EOF is an API return, not a
  resource ending or capability panic.
- `puts_contract` requires an in-bounds first NUL, the pointer ABI and
  a usable byte/unoriented stdout with designated writable state.
  A representation predicate and allocation-request relation remain
  explicit trusted inputs; a Boolean is not a proof of a native FILE.
  New stream roots must derive both their capability provenance (even
  for zero-length spans) and write coverage from old roots or this
  call's fresh objects, not unrelated caller memory. Aliasing is
  allowed: no disjointness or input-immutability promise is invented.
  Success accepts the string plus newline and returns a representable
  nonnegative int; EOF may follow any prefix, including the entire
  payload, and is normalized to 32-bit word bits.

The chosen first observation is **`StreamBytes`**, bytes accepted by
stdio, possibly only into a buffer. It is not `write(fd, bytes)` and
does not prove delivery to the kernel. A future flush may fail or
deliver pending bytes from earlier calls. Native trace coverage and the
relation between API acceptance and externally visible writes are still
trusted obligations to state, not theorems proved by `effects_preserve`.

### Campaign 4, milestone 2: guarded machine integration

[ExternalMachine.v](../rocq/theories/ExternalMachine.v) is a labelled
extension, not a change to `Semantics.step`, `inst_step`, `Machine.mstep`
or the extracted driver. Its registry maps unresolved names to trusted
contracts over a shared logical world.

- `external_site` recognizes direct global calls only, after defined
  and outside-subset functions, global data and the existing runtime
  `free` have taken precedence. The frame must not be doomed. Arguments
  are evaluated with the same `map_option arg_x` as the core, and the
  actual words are passed to `invoke`. Raw/indirect calls are deferred.
- Core machine steps lift silently, including safepoints. At an eligible
  external call, `external_core_safepoint` proves that a core step can
  only be a safepoint, leaving the call point in place. Every invocation
  checks preconditions in its actual post-safepoint state.
- Normal completion emits exactly the invocation's trace, uses its
  declared void/scalar/tuple channel (including empty/singleton tuples),
  and binds the values with `returned_env`. The continuation retains
  function, locals, callers and fuel, advances one instruction, and uses
  the invocation's exact memory, runtime state and logical world.
- Exit and resource endings retain that same final snapshot. Exit does
  not append a second `ProcessExit`; an ordinary main return does not
  become an exit event. Core `Done`, stuck and allocation refusal remain
  explicit terminal cases, guarded against intercepting external sites.
  Core terminals retain source **observation snapshots**, not a proved
  post-finalization memory: `Done` discards that memory in the old core.
- Missing contracts, failed evaluation, false ABI/preconditions and an
  incompatible return channel have explicit `ContractViolation` endings,
  not invented Fil-C traps. These are relational negation premises, not
  an executable decision procedure. `no_violation` requires rejection
  to be disabled at **every reached state**: a chosen silent safepoint,
  or a later repaired precondition, cannot hide an earlier failure.
  Admissibility does not imply a completed invocation exists; an admitted
  empty relation still fails the future native coverage obligation.
- `run_preserve` carries readiness, identity persistence, the evidence
  invariant and the single-definition invariant through finite labelled
  runs. Calls kill live access facts, so the evidence continuation uses
  `call_parked` and `parked_resume`. Single-definition scopes use only
  result-name updates and persistence, including for waiting callers.
  Legacy steps need no `spares` hypothesis: `step_inv` and
  `run_preserve` dropped it with the core machine's `mstep_inv`.
  Terminal snapshots claim no active-frame facts. `unchecked_is_core`
  says any `Unchecked` ending came from the old core; it does not prove
  arbitrary frees or doomed runs safe.

The regression proofs exercise actual transitions for `puts` success,
partial EOF and an output/write prefix before resource refusal; all
return channels; independent rejection with empty behavior; dispatch
isolation; doomed frames and safepoints; core endings; an exit trace;
and the order of two calls' events. Contracts remain abstract fixtures,
not native FILE/startup implementations. Completed calls are atomic;
the independent `ExternalCalls.prefix` relation has not been turned
into all of a native execution's intermediate machine states. Existing
`mstep_refines` still covers only the old machine.

### Campaign 4, milestone 3a: launcher entry memory

[Startup.v](../rocq/theories/Startup.v) states the readable projection
of the selected Fil-C launcher's argv/environment image: a checked,
pointer-aligned array including the sentinel, address bytes and auxiliary
capability for each slot, and an in-object first NUL for each string.
`startup_argument`, `startup_environment` and `startup_sentinels` expose
those facts for arbitrary finite contents, not just sample command
lines. Empty strings and an empty environment are included; the pinned
`filc_start_program.c` asserts `argc >= 1`. Its separate copying-size
lemma records the int `argc + 1` overflow boundary before checked size
multiplication. `main_void_entry` proves that the model's main(void)
frame ignores the launcher's three arguments, rather than restricting
the launcher to no arguments. Process-status conversion keeps the low
byte, but no new process-exit transition is claimed yet.

The retained [hi.c](../tests/c/prog/hi.c) is the census's exact source
program and now runs in the ordinary native-comparison matrix. Public
entry regressions reject mismatched argc, missing sentinel bounds,
nonnull sentinels, lost capabilities, wrong address bytes and missing
NUL. This is **not** yet a construction of copied, writable, fresh
startup objects or a proof of initial runtime readiness.

The remaining closure is split into small changes: first define the
stdout protocol (acceptance, ordered delivery/discard and allocation
fallback), then relate explicit libc roots and allocations to it, then
connect main's return to shutdown. Native FILE realization remains a
trusted obligation, not a guessed layout or a Boolean. Shutdown must
account for TLS destructors and dynamically changing/reentrant exit
registrations before stream cleanup, not just fold a fixed callback
list. A failed write may discard previously accepted bytes; acceptance
never promises descriptor delivery. Linking the pinned body and native
prefix coverage/adequacy remain necessary before `never_panics`.

### Campaign 4, milestone 3b: ordered stdout obligations

[Stdio.v](../rocq/theories/Stdio.v) defines a finite logical stdout
protocol, not a native FILE layout. Acceptance appends output
obligations; descriptor acceptance and output-error discard each consume
an exact prefix. A zero-progress output error leaves the obligations
unchanged. The error flag stays set across later output; its connection
to native `ferror` is not yet proved. Outstanding obligations are not
physical buffer contents, and descriptor acceptance is not durability.

`stream_accounting` proves that old obligations followed by new
acceptance equal all resolutions, in their actual interleaved order,
followed by the remaining obligations. Discarded bytes cannot disappear
from this accounting or be moved after all delivered bytes. The public
examples cover buffered acceptance without delivery, prior pending
output, partial delivery/discard followed by later output, sticky errors,
and empty/partial/full acceptance with EOF. They reject out-of-order
delivery, non-byte contents, success without the newline, and a
wide-oriented puts even when its run is empty and it returns EOF.

`puts_observation` summarizes **one whole call** as one cumulative
`StreamBytes` event, including the singleton empty-acceptance event on
EOF. It is not a concatenation-preserving projection of internal steps.
`protocol_puts_post` bridges this summary to the existing `puts_post`
only when supplied the independent string-memory and final readiness
premises. It proves neither invocation nor native refinement: effects,
representation, roots/delegation, allocator requests/fallback and
prefix coverage remain separate obligations. No memory, runtime or
machine interface changes, admits or new axioms are needed.

The source-selected buffering modes/capacities and ordinary malloc
failure fallback are deliberately not guessed here. Relating the
pinned `libio/ioputs.c`, `fileops.c` and `filedoalloc.c` paths to this
protocol, with actual capability-bearing roots and fresh allocation
evidence, is the next step; terminal resource refusal must retain the
existing runtime-refusal justification. Shutdown and startup object
construction/readiness remain open, so this still does not close `hi.c`.

### Campaign 4, milestone 3c: selected native stdout memory

[Libio.v](../rocq/theories/Libio.v) supplies a **partial memory view**
for the pinned x86-64 byte stdout file backend. It binds the actual
`_IO_buf_base`, `_IO_buf_end` and `_lock` slots' address bytes and aux to
explicit FILE, lock, errno and heap-buffer capabilities. Whole-root and
aligned field-slot checks are separate from decoding the slot contents.
The embedded byte at FILE offset 131 keeps the FILE's existing capability;
`short_buffer_delegates` proves that it needs no new object or authority.
Heap kind and liveness are not ownership and grant no permission to free.

The source/ABI evidence is the `coreRev` in `lib/filc-staging.json`, its
`projects/user-glibc-2.44/libio/{stdfiles,genops,filedoalloc,fileops}.c`,
`bits/types/struct_FILE.h` and NPTL `stdio-lock.h`. The installed Fil-C
compiler reports FILE size 216 and alignment 8. Pointer slots are at
56, 64 and 136; the short-buffer offset is 131. `_IO_FILE_plus` adds its eight-byte vtable
pointer; the private lock is `{ int lock; int cnt; void *owner; }`.
The [libc-output.c](../tests/c/prog/libc-output.c) probe checks the used
public layout constants, stat-selected allocated capacity and the
embedded one-byte unbuffered path against native Fil-C.

`file_capacity` is deliberately specialized to stdout descriptor 1 and
this pin's block-size configuration: successful stat uses a positive
block size below 8192, otherwise the capacity is 8192. Capacity and
allocated extent differ: capacity 8191 ends the buffer at base + 8191,
but `heap_req` reserves 8192 bytes. `Libio R.allocate_buffer` starts with
an actual successful `R.alloc` answer and proves freshness, readiness,
an authorized allocation effect and the resulting buffer authority.
`buffer_refusal` requires the actual runtime refusal; the bounded request
cannot justify `TooBig`. Neither lemma installs pointers or flags yet.

The selected allocator distinction is now explicit. Generic libio falls
back to `_shortbuf` if its malloc returns NULL, but this glibc's
`malloc/malloc.c:__libc_malloc2` forwards directly to `zgc_alloc`.
`filc_native_zgc_alloc`, `filc_allocate` and `verse_heap_allocate` reach
the runtime's no-return allocation failure, not NULL. The separate
`pinned_choice` excludes the generic NULL branch; byte-unbuffered setup
still uses the embedded buffer without allocating, and an existing
buffer has priority. These are branch facts, not a native coverage proof.

Installation is the following milestone. This memory view alone is not
complete FILE validity, exhaustive native roots or a `puts` realization.

### Campaign 4, milestone 3d: install the selected buffer

`Libio R.setup_short` and `setup_heap` now compose the **NoBuffer** case
of pinned `genops.c:_IO_setb`: store the base and one-past end with their
capabilities, then set `_IO_USER_BUF` for the embedded byte or clear it
for the allocated buffer. The four-byte mask preserves every other
flags bit. Null initial slots exclude the native old-buffer release;
this is not arbitrary replacement or proof of buffer ownership.

The embedded setup performs only authorized local stores, with no
allocation request or new identity. Heap setup requires the actual
successful allocator answer for the original capacity, preserves every
old root across fresh allocation, then installs the pointers and flags.
Both theorems establish an effects path, runtime readiness, identity
persistence, the new checked `stdout_memory` view and outgoing-root
delegation. Shared byte-store, pointer-store and disjoint-slot lemmas
prove serialization and auxiliary metadata explicitly, not just address
agreement. No new runtime axiom or core machine change is needed.

The installed-memory regressions exercise capacity 8191 with extent
8192, both flag updates, the retained FILE/heap capabilities, the
unchanged lock pointer and nonzero errno contents, and rejection of
dead or undersized buffers.
These are model regressions, not evidence that native libc realizes the
whole contract. Existing native layout and allocation/bypass probes
remain the pin evidence; the latter also check the null initial slots
and the selected `_IO_USER_BUF` outcomes.

Selection remains conditional on the selected byte/file backend; the
cause-indexed `pinned_choice` is not native dispatch or allocation
evidence. In particular, installation does not model the earlier
`_IO_file_doallocate` line-buffer flag update or prove that mode, stat
and descriptor observations select that call. It also does not invent
a NULL return when the runtime refuses allocation.

Startup construction and shutdown follow. Full FILE validity, backend
dispatch, flags/orientation and lock state, pending-byte representation,
native effects/prefix coverage and protocol scheduling remain open.
For example, storing `THREAD_SELF` in `lock.owner` needs a capability
source beyond these writable spans. `hi.c` is not yet closed; no native
trap-freedom or adequacy theorem is claimed.

### Campaign 4, milestone 4a: construct one startup string

`Startup R.copy_string` now constructs a string from the launcher's
native input bytes instead of assuming a final model string. It requires
the original `strlen + 1` request to be authorized, within the allocation
limit, and actually answered by `R.alloc`. The byte-copy path includes
the terminating NUL, creates no pointer capability from raw bytes, and
establishes a checked readable **and writable** string, runtime readiness,
identity persistence, and its call-born allocation history.

`copied_string_old_object` frames bytes and auxiliary capabilities in
**every** old object's current bounds, not just an enumerated root list.
The copy leaves all old regions unchanged. This is the frame needed to
retain the preallocated argv table and earlier strings during subsequent
copies; persistence alone would not prove their contents unchanged.

Payload lists denote bytes before the first NUL: any value from 1 through
255 is allowed, including high bytes, and the empty list needs one byte
for its NUL. A list containing zero is not this representation of the
native input; it is not a claim that native argv traps on an embedded
zero. The success theorem compares the original size before rounding,
as `filc_prepare_allocate_object` does. Runtime refusal and oversized
requests retain the existing resource rules, not successful NULL copies;
this slice does not yet prove coverage of the launcher's failure paths.

Model examples cover empty/high-byte payloads, a 17-byte request with
32-byte extent, retained old pointer-slot capabilities, and missing NUL
bounds. The [libc-entry.c](../tests/c/prog/libc-entry.c) probe re-execs with
an empty argument and high bytes, under both populated and empty
environments, and performs volatile writes to copied NUL bytes.

Next, allocate each pointer table first and thread the actual runtime
state, memory and cumulative born list through the forward string-copy
and pointer-store loop. Preserve the zero sentinel and derive the full
`startup_at` image; retain argv's signed `argc + 1` restriction and prove
environment-size arithmetic separately. Auxiliary-vector construction,
libc/TLS/stdio readiness, constructors, shutdown and native coverage
remain open. This conditional string suboperation does not close `hi.c`.

### Campaign 4, milestone 4b: construct argv and environment tables

`Startup R.copy_vector` allocates the pointer table first, including one
sentinel slot even for an empty vector. `copy_slots` then executes the
forward allocation, NUL-inclusive copy and pointer-store loop, threading
the actual runtime state and cumulative born list through every step.
Each slot receives both address bytes and its allocator-created `Obj`
capability. The zero sentinel comes from fresh allocation and is framed
through the loop, not restored by a fictitious final write.

`copy_slots_correct` carries the live, already-born table identity,
aligned cursor, bounds through the sentinel, and fresh separation from
earlier strings. `startup_frame` preserves every old region exactly and
bytes/auxiliary metadata outside the remaining slots. At vector entry
even the table is new, so `copy_vector_correct` frames **all** old
objects, alongside effects, readiness, identity persistence, the checked
readable vector and a writable table span. `copied_startup` composes
argv and environment construction into `startup_at` while preserving
argv through the environment allocations.

The successful construction remains conditional on actual allocator
answers, valid pre-NUL payloads and authorized original sizes within the
allocation limit. `None` does not classify a native failure. Argv retains
the signed `argc + 1` restriction (`argc < INT_MAX`); the environment's
legal original table size instead implies the selected size_t count,
increment and multiplication bounds, without a signed-int limit.

Executable regressions distinguish table-first and forward allocation
order, asymmetric/empty/high-byte strings, slot stride and capabilities,
both sentinels, empty and populated environments, and old pointer/byte
framing. The native re-exec probe covers both environment cases.

This is memory construction, not coverage of the entire launcher: native
obtaining/tracking of `main` between the two loops, auxv, libc/TLS/stdio
initialization, constructors and failure paths still need accounting.
Shutdown's lifecycle follows below; no `hi.c` closure or native
trap-freedom is claimed.

### Campaign 4, milestone 4c: shutdown lifecycle and main return

[Shutdown.v](../rocq/theories/Shutdown.v) gives the serialized lifecycle
of the selected user-glibc's exit path. Its TLS destructor hook is empty
at this pin. Registrations are distinct instances, even for the same
function: pop-before-call records the consumed token, successful dynamic
registration pushes a fresh token, and recursive exit abandons the
active callback while replacing the signed status. Remaining callbacks
see that new status. Proofs establish invocation uniqueness, exact
consumption history, sticky registration closure, and stdout accounting
through finite prefixes. There is no eventual-completion theorem.

Cleanup projects delivery and output-error discard, without promising
that every byte is delivered or even settled. Both soft and hard
handoffs retain outstanding obligations. Hard exit neither invokes
handlers nor invents a flush/discard; it installs its own `_exit`
argument, including when it replaces an enclosing exit's status during
a callback or cleanup. Successful registration is
conditional; registration failure, callback memory effects, concurrent
finalization, `dlclose`, `__cxa_finalize` and quick exit are not represented
by this stack protocol. Cleanup reentrancy and arbitrary backend
callbacks are likewise not coverage claims.

The boundary is deliberately **host-exit handoff**, not native process
termination: `filc_native_zsys_exit_soft` leaves Fil-C and calls host
`exit`; its hard counterpart calls host `_Exit`. Host handlers, loader
finalization and host stdio therefore remain an explicit, uninstantiated
completion contract. Only its witnessed observation contributes one
`ProcessExit`. This does not prove arbitrary external callback traces
exit-free; later composition must exclude exit events from returning
callback/cleanup traces and transfer recursive exit to the lifecycle.

`main_return_step` justifies the retained core snapshot for a real
non-doomed, top-level W return **with no locals**, because invalidation
is then exactly identity. It adds no successor to the terminal state of
`ExternalMachine`. Main's result is interpreted as a signed 32-bit C int
before shutdown: -1 reaches callbacks as -1, although the final process
status is 255. Doomed/live-local returns cannot use this bridge.

The native exit probe now distinguishes new-handler precedence and
recursive exit with a signed -1 observed by `on_exit`, followed by
buffered-output cleanup, and a handler's `_exit(98)` replacing
`exit(31)` without cleanup. The symbolic examples also cover duplicate
function registrations, token reuse rejection, partial delivery/error,
hard exit's unflushed output, and the concrete main-return bridge.
This closes a lifecycle component, not callback/native cleanup
realization, host termination, full entry readiness or `hi.c` closure.

### Campaign 4, milestone 4d: the hi application body

[Hi.v](../rocq/theories/Hi.v) now models the actual two-instruction
shape emitted for `tests/c/prog/hi.c`: copy the read-only literal to
`v0`, call `puts` with that temporary and a W result in `v1`, then
return zero. Its module initializer actually constructs the literal's
global object, bytes and capability. `main(void)` accepts arbitrary
launcher argc/argv/environment words and ignores them; the proof does
not replace the entry contract by an empty argument vector.

`hi_finite_safety` covers **every finite labelled application run** from
the stated entry invariant, not only an exhibited successful run.
Terminals are return zero, fuel exhaustion, or declared resource
endings. `hi_all_calls_admissible` proves symbol coverage, ABI and the
NUL-inclusive string precondition at every reached external call,
independently of a completed invocation's existence. Failed-contract
rules remain enabled in the machine; the proof rules them out from
this entry invariant rather than deleting executions.

The literal survives all runtime safepoints by the existing lifetime,
rooting and non-moving axioms: it is GlobalData, not a freeable heap
object. Opaque libc state needs a separate **stdio-stability premise**
at both the global-copy and puts-call safepoints. This premise is
inhabited by the interpreter runtime, whose safepoints are identity.
It is not derivable for every unrestricted Runtime, and a regression
shows freeing the fixture's protected libc root destroys its
representation. The native contract table already excludes hostile
signal handlers and racing frees; no stronger global Runtime axiom is
introduced here.

Every represented puts completion is an integer return or permitted
resource ending. Any integer result, including EOF after empty,
partial or full acceptance, resumes the actual no-locals `return 0`
with the invocation's exact final memory. Missing registry coverage
still produces a specification violation without needing an invocation.

This is the **source-shaped application theorem relative to trusted
entry, libc and environment contracts**, not yet whole-program closure.
Pinned lowering equality, native prefix coverage, stdout continuity
from puts to shutdown, registration inventory and one-shot host
completion remain explicit next obligations. The body theorem alone
does not promise puts completion, delivery, process exit or native
trap-freedom.

### Campaign 4, milestone 4e: coupled stdout endpoints

[Composition.v](../rocq/theories/Composition.v) strengthens the trusted
puts contract with a logical world containing the existing stdio
capability roots, **one exact stdout protocol state**, and the pending
exit-registration inventory. Every prefix, including unfinished and
resource-ending prefixes, carries a stream-run witness between its
actual endpoints and preserves that inventory. Normal completion also
ties the returned integer and acceptance summary to a `puts_protocol`
witness over those same endpoints. The source string is always read in
the original invocation memory, not its endpoint memory.

Forgetting stdout and registrations projects both prefixes and completed
invocations into the existing puts contract, retaining the exact memory
effect path, requests and resource-failure evidence. This implication is
**one-way**. Native satisfaction of the stronger contract is a trusted
specification obligation, not a consequence of native satisfaction of
the old contract. The logical stream relation does not implement FILE
or establish a native buffer interpretation.

The endpoint lemmas establish FIFO accounting, stream well-formedness,
nonwide preservation, sticky error and exit-free observations. Raw
prefixes need explicit source well-formedness: they do not implicitly
include call admissibility. An empty observation forbids new acceptance
but may deliver old obligations; it does not imply unchanged stdout.
Each summary is cumulative for one original call. It must not be
concatenated with another summary as if they were incremental writes,
or used to restart puts at the observed endpoint.

Examples exercise empty/partial/full EOF, partial acceptance followed
by a genuine oversized-allocation resource ending, silent delivery of
prior output, inventory mutation and wide-entry rejection. Distinct
delivery/discard histories can have the same endpoint when error is
already set; the contract does not identify those histories or promise
that each prefix extends to a completed call.

Next, the outer application/shutdown relation must establish these
stronger preconditions at every reached call, retain the exact stdout
and inventory through main's actual return, and consume host completion
once. Inventory equality and distinct tokens are **not callback
validity**: callable targets, ABI, retained arguments and memory
preconditions still require a trusted shutdown-ready contract at the
exact post-puts memory. No native closure claim is made here.

### Campaign 4, milestone 4f: conditional outer execution

[Program.v](../rocq/theories/Program.v) proves the stronger coupled
world's preconditions at **every reached application call**, including
arbitrarily repeated permitted safepoints. Its projection handles the
machine's rejected-call rules explicitly: one-way invoke projection
alone would not justify this theorem, because the richer contract has
additional preconditions. Every finite stopped application still has
the body theorem's return-zero, fuel or resource classification.

An additive outer machine now has application, shutdown, unfinished
call-observation and finished phases. The main-return bridge requires
the actual non-doomed no-locals return site, retaining the exact
runtime, memory, stdio world, output obligations and registration list.
`puts_shutdown_closed` names the trusted libc/entry obligation that
establishes shutdown readiness at **every returning puts endpoint**
in its selected entry domain (restricted in milestone 4g below);
`returning_puts_shutdown` derives the real return-zero bridge from it.
Readiness is not inferred merely from equal callback tokens or hidden
by requiring it only on an edge that might never exist.

Each successful shutdown segment selects an opaque contract and its
argument/ABI obligations, supplies an actual contract effect-prefix
witness and endpoint relation, and preserves shutdown readiness.
`shutdown_ready_admits` separately states selected-action admissibility,
independently of an effect witness. Callback native ABI and retained
argument validity remain inside that trusted boundary; dynamic
registration needs its own admission condition. Recursive and hard
exit are control transfers, not falsely returning callbacks.

Action/trace compatibility is explicit: starting a callback is not
executing its entire body; callback output is represented by later
output actions. Only acceptance actions emit stdout acceptance events;
delivery/discard/error and pure lifecycle actions do not. Actual effect
witnesses preserve allocator readiness and object identities, while
each segment's stdout projection retains FIFO accounting.

Host completion is tied to the entire handoff snapshot and consumed
into an outer terminal. `at_most_one_exit` proves that **every finite
represented execution** from the application invariant contains at
most one process-exit observation. Unfinished puts observations are
terminal leaves tied to the independently admissible original call and
its evaluated argument, not restarted calls. Resource and original
inner-machine terminal observations have no shutdown successor.

An inhabited fixture traverses actual main entry/copy/call/return,
identity-memory shutdown segments and one host completion. It retains
accepted bytes as outstanding, deliberately showing that acceptance is
not guaranteed delivery. It is a logical contract fixture, not native
libc or host coverage. Successful shutdown segments do not yet cover
blocking/resource leaves inside callbacks/cleanup. Native launcher and
stronger libc contract satisfaction, pinned lowering correspondence,
native shutdown realization and host completion remain open.
`application_never_panics` uses Campaign 3's shared `failure_ending`
classification from [Panics.v](../rocq/theories/Panics.v), the same
classification used by its closed-module `never_panics`. This conditional
labelled application theorem is not yet unconditional native safety.

### Campaign 4, milestone 4g: reached closure and generated hi

The closure premise now takes an exact initial application state and
quantifies over **all** returning invocations at calls reached from it
by the ordinary inner `M.run`. That reachability does not use shutdown
readiness, the outer return bridge or the closure premise itself.
`returning_puts_shutdown` lifts this actual prefix once, retaining its
trace before the returning call's trace and transferring the exact
endpoint. No arbitrary callback inventory becomes eligible merely
because its tokens are distinct. `body_run_inventory` proves every
application run preserves the entry's registration list; the empty-list
fixture cannot reach a call with even one substituted registration.

The entry's body invariant and safepoint stability still establish
reached-call admissibility **independently** of closure and invocation
existence. Selecting an invalid or stopped initial state can make the
closure premise vacuous; it does not establish a valid entry or a
native safety result. The inhabited actual-entry fixture is retained.
`application_stopped_never_panics` extends the shared `failure_ending`
classification to stopped application endpoints of the outer machine,
without closure or host-completion assumptions. It does not cover
disabled shutdown actions or prove eventual completion.

[HiArtifact.v](../rocq/theories/HiArtifact.v) proves by reflexivity that
decoding the generated `HiCode.hi_term` gives exactly `Hi.hi_module`.
Campaign 3's shared `rocq/programs.sh` gate regenerates that term from
`tests/c/prog/hi.c` using `cc-ir`, `-O outcomes` and
[gallina.pl](../rocq/gallina.pl), and
rejects any drift. The routine Rocq check runs this gate. This closes
the gap between the hand-written body and the current checked compiler
artifact, including literal bytes and call temporaries; it is not a
proof of C lowering, native interpreter refinement or libc realization.
Generated `HiCode.v` is never hand-edited. Native startup, stdio,
shutdown resource/blocking coverage and host completion remain open.

### Campaign 4, milestone 4h: every launcher input at application entry

`HiProgram R.hi_launcher_words_safe` in
[HiArtifact.v](../rocq/theories/HiArtifact.v) proves that main is defined
and that the actual launcher words produce a call frame. For every fuel
and ready supplied entry runtime state, all reached external calls are independently
admissible and every stopped application endpoint of the outer machine
is nonfailure under the shared classification. Entry-memory/stdio
validity, logical world validity and safepoint stability are explicit
premises; shutdown closure and host completion are not assumptions of
this application-only safety theorem.

The exact allocator state after startup is retained with its memory,
not reset to `R.start`: startup's `copied_startup` exports readiness at
the resulting allocator state, which need not hold at the original start.

There is no short-string, C-locale or empty-argv restriction. The theorem
is stronger than requiring `startup_at`: main(void) ignores all three
launcher words. This does **not** establish native launch for malformed
words or construct its libc/TLS image; startup's own preconditions and
resource outcomes still apply before entry. Native realization and
shutdown blocking/resource coverage remain open.

### Campaign 4, milestone 4i: named trusted entry and host contracts

The libc trust policy explicitly includes the pinned launcher,
libc/TLS initialization and host completion. In
[HiArtifact.v](../rocq/theories/HiArtifact.v),
`trusted_entry_contract` names the successful-entry image, including
startup vectors, exact allocator-state readiness, module literal and
opaque libc/stdio validity. `trusted_entry_never_panics` derives
application-only nonfailure from it and the stated safepoint-stability
premise. It is not a theorem that native startup supplies every image
or always succeeds. Refusal and unfinished startup are not normal entry.

`trusted_host_contract` retains an explicit successful-completion
witness at the exact ready handoff, rather than deriving termination
from readiness. `trusted_host_completion_step` permits one terminal
low-byte exit observation under this contract. The remembered snapshot
and pending output remain unchanged; they do not describe postmortem
memory or prove delivery. The trusted boundary owns host handlers,
loader finalization and host stdio under the observation policy stated
in [libc-contracts.md](libc-contracts.md#trusted-entry-and-host-boundaries).
Host callbacks re-entering modeled Fil-C require their own contracts.

The extended [libc-entry.c](../tests/c/prog/libc-entry.c) probe checks
initialized TLS and usable errno/streams in a constructor and fresh
re-execs. [libc-exit.c](../tests/c/prog/libc-exit.c) now observes fresh-exec
main return, soft exit and both hard-exit names through wait status and
exact descriptor bytes, with signed/wrapping statuses and handler/flush
distinctions. These are finite native probes, **not proofs of the native
implementations**. The contracts are listed separately in the
[trusted base](runtime-axioms.md#trusted-libc-outside-the-runtime-module-type);
no new axioms or core machine rules were added. Lifecycle prefix/resource
coverage remains the next closure slice.

### Campaign 4, milestone 4j: terminal shutdown prefixes and refusals

[Program.v](../rocq/theories/Program.v) now represents unfinished
shutdown segments and genuine requested allocation refusals as separate
terminal leaves. Each keeps the exact endpoint runtime, memory and
stdio world, the original selected lifecycle snapshot, the selected
action and the observed stdout history/state. The original snapshot
is provenance, **not** a statement that its phase or inventory describes
native endpoint memory. Neither leaf can restart its cumulative prefix,
continue cleanup or use the host-completion rule.

Selection and admission are independent of completion: an enabled
`shutdown_step`, source shutdown readiness and the action's ABI and
argument preconditions are required. Unfinished leaves need the actual
selected contract's effect prefix; resource leaves need its actual
`invoke` ending in `CallResource`, including a permitted request and
real refusal evidence. Neither requires `action_post`, successful target
readiness or a completed lifecycle transition. Actual effects preserve
allocator readiness and object identities. Refusal reasons satisfy the
shared `failure_ending` classification, and the existing application
safety and at-most-one-exit theorems continue to hold.

Partial stdout histories conservatively stay within the selected action:
acceptance, delivery and discard cannot change families or exceed the
selected byte prefix; an output-error segment observes zero or one
error; control actions have no output history. A real `stream_run`
supplies FIFO accounting, well-formedness and sticky error. Only
acceptance has a cumulative stdout event; no partial leaf emits exit.
Delivery and discard histories remain distinct even when their logical
endpoints coincide.

Logical fixtures cover unfinished TLS with no successful post/target
readiness, partial FIFO delivery, and a resource refusal after both
allocation and partial acceptance. Regressions reject control output,
excess acceptance, wrong-prefix delivery, delivery/discard substitution
and unrequested resource endings. These are **not native blocking or
refusal coverage proofs**. Mixed-operation native segments, independently
valid callback admission and a selected complete boundary still need
instantiation; absence of a prefix witness proves neither safety nor a
native trap. The new rules add no axioms and leave Machine/Runtime alone.

### Campaign 4 milestone 4k: selected lifecycle segment contracts

`Selected.v` separates memory/world-indexed `libc_valid` from exact
allocator readiness. Every selected lifecycle action specifies capability
sources, writable spans, owned heap releases, allocation requests, finite
prefixes and its documented panic set. These permissions are independent:
a readable callback argument is not automatically writable or owned.

The contract's precondition requires validity, an independently selected
action and an enabled logical edge. `selected_admits` establishes ABI and
preconditions **without an invocation witness**. Selection is intentionally
restricted: the logical register rule's fresh token does not authorize
an unknown callback. The older all-actions `shutdown_ready_admits` remains
available, but is not falsely asserted for a restricted registry.

A successful contract post supplies `segment_finish`: the exact lifecycle
edge, its acceptance observation and valid endpoint representation.
`invocation_realizes` extracts the **same invocation's** effect prefix,
born list and post, deriving allocator readiness from actual effects.
Callers no longer independently supply action-post and target-readiness
premises. The empty-argument, void-return ABI is a logical segment marker,
**not a native C callback ABI or a return from exit/_exit**. Unfinished
prefixes and resource leaves remain terminal and cannot use this adapter
as a continuation.

`entry_rep` strengthens puts' opaque invariant for the actual entry
inventory, retaining its pending callback validity for every well-formed
logical output queue. This is a conservative representation requirement,
not physical FILE-buffer reconstruction. `reached_puts_closed` combines
that contract guarantee, exact inventory preservation, stream continuity
and runtime preservation to discharge the reached-call shutdown-closure
obligation. Safepoint stability and the selected entry image remain
explicit; equal token lists alone still do not establish callback validity.

Inhabited logical fixtures use a nonempty callback inventory with a live
retained argument and reject unknown callbacks, expired argument bounds,
argument writes and unowned releases. Completed delivery, error and
discard segments compose through exact intermediate snapshots, never by
resuming an unfinished leaf. These fixtures are **not pinned native
callback implementations**. Admission and specification consequences are
proved; native representation satisfaction, action selection/coverage and
valid native cutpoints remain trusted obligations to instantiate and probe.
The independent partial-output histories of milestone 4j still do not
prove exact native queue correspondence. No unconditional hi.c closure,
native totality or native implementation proof is claimed.

### Campaign 4 milestone 4l: the pinned exit registry memory view

`ExitMemory.v` describes a **snapshot**, not a registry executor or native
satisfaction proof. The pinned `stdlib/exit.h` declarations, extracted and
compiled with Fil-C, give 32-byte entries, 1040-byte blocks, next/idx/fns
offsets 0, 8 and 16, and function/argument/DSO offsets 8, 16 and 24 within an entry.
This measures the source-selected declarations, not hidden runtime object
locations. Synchronization and stability between cutpoints remain separate.

The checked containing-object access and decoded pointer capabilities are
both required. Chains are finite, null-terminated and identity-distinct.
`idx` counts represented physical slots, **not live callbacks**: free and
reserved slots are skipped, while unknown flavors fail the view. Blocks
scan head-first, each block scanning slots downward. This pin stores
`atexit` registrations as `ef_cxa` with null argument/DSO; adapting that to
logical `AtExit` still requires its calling-convention contract.

Pending callbacks and the detached active callback require independent
admission/argument specifications. A decoded `Fn` capability alone is not
one. Slots at or above decremented `idx` may retain stale payloads, and
consumed callback arguments need not remain live. Ghost registration tokens
are not reusable slot addresses. Writable spans remain independent of the
read-only view. Block release eligibility additionally needs explicit
ownership, an exhausted live Heap base with enough extent, unlinking and a
distinct nonempty successor chain; the last node is retained even if Heap.
The predicate does not itself perform a release or prove its footprint.

Model fixtures inhabit a registry with a free hole and check reversed
multi-block projection, stale payload exclusion, detached admission and
rejection of excessive idx, wrong link/function capabilities, unknown
flavors, repeated blocks and unowned/last-node release. The native
`libc-exit.c` probe checks 31, 32, 33 and 65 registrations with asymmetric heap
arguments, reverse callback order, exact status and descriptor bytes,
freeing each argument after consumption. Startup registrations and holes
mean these counts do **not** measure exact native slot occupancy; direct
callback writes are not stdio acceptance observations. These are finite
counterexample probes, not universal implementation proofs. Selected
startup callback specifications, native registry representation satisfaction,
locking/stability and lifecycle segment coverage remain to instantiate.

### Campaign 4 milestone 4m: constructing the pre-callback pop

`ExitMemory.v` now constructs the selected native metadata writes for one
nonempty head block: decrement `idx`, then clear the removed flavor for
`ef_cxa` only. Payload bytes, every auxiliary capability, regions and block
identities remain unchanged. Exact byte framing is proved from the stores,
not inferred from the larger permissions of an arbitrary contract effect.
The original capacity and containing alignment justify the eight-byte field
checks; independent narrow writable spans justify an effects path over any
runtime, with no allocation or release, at both the index-only and final
cutpoints. Captured payload capabilities come from complete checked source
slots, separately from write permission and callback admission.

Registry preservation additionally requires that the head cell and other
block storage do not overlap the popped block. Distinct identities alone
are insufficient: an inhabited counterexample puts the head cell inside
`idx`, so its initially consistent pointer is corrupted by decrementing it.
The snapshot predicate is not silently strengthened; separation is an
explicit construction premise. An empty block cannot supply a selected pop.
An exhausted endpoint is not permission to unlink or release the block.

Free/reserved slots stutter logically, without inventing a shutdown action.
An installed slot gives the existing `InvokeCallback` edge from the actual
pending projection to the detached active registration; independent token
uniqueness is preserved. Memory-indexed callback admission needs a general
footprint-stability rule for **all** pending and active callbacks. The
inhabited fixture discharges it for known callbacks and checked retained
argument data outside the writes; a specification depending on `idx` is
explicitly rejected. Other fixtures cover a preserved second block, cxa
flavor clearing with untouched payload capabilities, and missing write
authority. The native boundary probes remain milestone 4l's finite evidence;
they cannot independently observe these hidden metadata writes.

This is a constructed **pre-callback entry cutpoint**, not native indirect
dispatch, callback ABI correctness or callback execution. No traversal loop,
re-registration, recursive exit, allocation, unlink/free, lock implementation,
selected-segment instantiation or universal native cutpoint coverage is
claimed. The next construction slice is exhausted-block unlinking with
explicit release ownership and non-target framing; native callback/entry
instantiation and unconditional hi.c closure remain open.

### Campaign 4 milestone 4n: exhausted-head unlink without retirement

`ExitMemory.v` constructs the head pointer store from an exhausted block's
checked next slot. It copies both address bytes and the successor capability;
the original readable source slot supplies capability authority, separately
from the writable eight-byte head root and aligned store access. The actual
local effect preserves readiness and identity over any runtime, without
allocation or release. Regions are exactly unchanged, bytes are unchanged
outside the head's eight bytes, and shadow is unchanged except at the head.

Explicit head-cell separation from represented block storage preserves the
checked suffix and the detached exhausted block. A singleton is unlinked
to canonical null, **not left in the registry**; its allocation stays live.
Unlink contributes no logical callback action and leaves the pending order
and detached active registration unchanged. Admission transport for all
pending/active callbacks requires a general arbitrary-snapshot frame rule
that permits the head shadow update. Pop's globally unchanged-shadow rule
cannot justify it. A retained-argument fixture discharges the new rule;
a predicate observing the old head capability is rejected.

Inhabited singleton/multi-block fixtures check allocation retention,
successor address and capability, and the callback-bearing suffix. Controls
reject bytes-only pointer stores, absent write authority and overlapping
head/suffix storage: distinct block identities alone admit a snapshot whose
head store corrupts the older block's index. This is a selected metadata
construction, not native execution, synchronization or lifecycle coverage.
No done-flag store, cleanup transition, callback dispatch, or retirement is
claimed. Retirement needs a separate identity-aware lifetime frame, including
head-object exclusion and callback dependencies; arbitrary runtime free
axioms do not supply precise non-target preservation. Native satisfaction,
selected lifecycle segment instantiation and unconditional hi.c closure
remain open; libc stays trusted behind its stated contracts.

### Campaign 4 milestone 4o: conditional whole-model hi composition

`Selected.trusted_hi_completion` connects the named successful
`HiProgram.trusted_entry_contract`, the generated application's actual
reached returning `puts`, a finite chain of selected shutdown **invocations**,
and `HiProgram.trusted_host_contract` at the exact resulting handoff.
The same entry inventory, runtime state, memory, logical stdout and retained
callback specifications cross those boundaries. The entry domain is any
well-formed argv/environment satisfying that trusted image, not an assumption
of an empty registration inventory. Safepoint stability remains explicit.

`Selected.normal_run` names each logical shutdown target but does not ask
the caller to supply `Program.realizes`, endpoint validity or endpoint runtime
readiness again. Those follow from the same invocation's effect path and normal
post. Fixed-action target uniqueness in `Stdio.v` and `Shutdown.v` identifies
the extracted target with the next cutpoint; neither transition system changes.
The full trace includes application and shutdown observations followed by the
one host-exit event. Separately, `trusted_hi_observations` covers represented
finite observations, including unfinished/resource leaves: runtime readiness,
at most one exit event, and application-stop exclusion under the shared
`failure_ending` classification. It does not assert eventual completion.

An inhabited logical fixture supplies real argv/literal/stdio/argument memory,
a nonempty eligible callback inventory, an actual returning buffered `puts`,
and three selected invocations (TLS completion, callback entry, hard exit).
Its callback changes status to 258, whose observed process status is 2;
accepted bytes remain outstanding, rather than being silently delivered.
The existing unknown-callback and missing-host-witness controls still reject
admission/completion. The host fixture fixes the full runtime/memory/world
and handoff snapshot, rejecting a changed status or invented empty queue.
This is a logical composition instance, not evidence that the fixture callback
executes natively or that native hi takes this path.

This closes the **conditional composition** gap, not native adequacy. For the
pinned launcher/libc/TLS/host boundary, the following obligations remain distinct:
independent source-state action selection and callback admission; native
satisfaction of the selected contracts and their effect permissions; and
exhaustive observation coverage, including resource refusal, unfinished work
and host handoff. Existing libc entry/exit probes are finite evidence, not
proofs of these universal obligations. A theorem over existing invocations
cannot establish coverage by omitting executions without such witnesses.

Libc stays trusted behind these contracts. Internal registry scanning, unlink,
retirement and done/lock work belong within a selected native segment before
the next genuine logical cutpoint, not new outer lifecycle stutters. They may
not hide callback output, re-entry or control transfers. The metadata pop/unlink
constructions remain useful supporting evidence, not prerequisites for a libc
executor. No native callback dispatch, universal segment satisfaction/coverage,
termination or unconditional native `never_panics` theorem is claimed.

### Campaign 4 milestone 4q: the bounded strnlen contract kind

`ExternalCalls.v` adds a pure `strnlen_contract` over any logical world.
Its `bounded_length` premise requires a canonical size_t maximum, a live
Obj/Ro capability, and readability only through the first NUL before that
maximum, or exactly the maximum bytes if all are nonzero. A NUL at byte n
is not required. An early NUL permits even SIZE_MAX without requiring the
unused address+n to fit or n bytes to be readable. Zero count permits a live
one-past pointer but not null, expired or forged authority; the raw zero-size
access check alone would incorrectly admit a freed empty object's base.

The return and count ABI use class L. The result is unique and within the
maximum; all bytes before it are in 1..255, not arbitrary nonzero Z values.
Every admitted input has a permitted normal invocation using the reflexive
effect path. All represented completions return that bounded result with
unchanged exact memory/world and no observations; no writes, releases,
allocations, resource outcomes or exit are permitted. Empty capability sources
mean no capability propagation, not an assertion of no byte reads. Runtime
readiness bounds the consumed interval to the address space, without bounding
the unused maximum. These are specification/nonvacuity results, not native
termination or an implementation of the scan.

Fixtures cover an exact-bound nonterminated high-byte object, an early NUL
at the last readable byte with SIZE_MAX, zero-count read-only one-past, and
rejection of positive one-past scans, null/freed authority, malformed bytes,
wrong results and wrong ABI/count kinds. The extended `libc-regions.c` native
probe independently checks short objects, unaligned high bytes, huge bounds
and zero-count writable/read-only one-past pointers. The pinned strnlen source
delegates to memchr; its generic implementation and multiarch alternatives
need not perform only byte loads. Passing finite probes does not prove native
satisfaction of the narrow API premise. Interpreter registration, additional
Hello functions and universal native satisfaction remain future slices.

### Campaign 4 milestone 4r: bounded pointer-returning memchr

The next Hello contract kind is a pure bounded binary search.
`memchr_input` independently admits a canonical class-W int pattern and
class-L size_t count, a live Obj/Ro capability reading the entire count,
and byte cells in 0..255. Unlike strnlen, an immediate match does not
waive an unreadable suffix. Zero count permits live one-past authority,
but not null or freed authority; invalid inputs are failed obligations,
not invented native traps. Comparison uses the int pattern's low byte,
so both 511 and the normalized representation of -1 search for 255.

`memchr_result` is the first matching offset with exactly the input
capability, or null with no capability on a miss. Merely requiring an
available return capability would be weaker: a source span can also
contain complete stored pointer slots. The postcondition therefore fixes
the pointer itself, and requires a pointer word rather than any class-P
word. Its only capability source is the input span; there are no writable
roots, releases, allocation requests, resource endings or observations.
Every represented completion retains exact memory and logical world.

Constructive finite first-match existence and result uniqueness yield a
permitted returning invocation for every admitted input, without requiring
the caller to supply a result in its precondition. Runtime readiness bounds
the full readable interval. Fixtures reject later matches, false null,
same-address capability loss/amplification, unreadable suffixes, invalid
zero-count lifetimes and wrong scalar/ABI domains. They cover binary zero,
high-byte conversion, a miss and a returning read-only pointer invocation
from ready memory. Native probes distinguish competing matches, last-byte
hits, exact-bound misses and zero count at an aligned allocation's end.

These results specify trusted libc, not its execution: no libc executor,
interpreter registration, native satisfaction, exhaustive coverage or native
termination is proved. The pinned generic source's wider reads and pointer
reconstruction still require separate implementation justification.

### Campaign 4 milestone 4s: bounded memcmp and signed result freedom

`readable_bytes` extracts memchr's existing full-span premise without
changing its domain, contract or fixtures. It carries the canonical size_t
count, live Obj/Ro authority, complete readable interval and 0..255 byte
domain. strnlen deliberately retains its different early-NUL premise.
The shared extent theorem bounds a readable interval under runtime readiness.

The memcmp contract requires two such spans in the same memory. They may
overlap or be identical; neither side's authority is waived at zero count,
nor does an early difference waive either unreadable suffix. Its ABI is
P/P/L arguments and a class-W result, even when discarded. The byte-order
relation describes the first differing unsigned-byte pair, or equality
throughout the count. Constructive finite existence and order uniqueness
are independent of invocation existence.

The result is any canonical W bit pattern whose signed reading has that
order's sign. It is not constrained to the byte difference, to magnitude
at most 255, or to precisely -1, 0 or +1. Only its sign is unique, not the result
word. Every independently admitted input has a permitted returning witness;
all represented completions preserve exact memory/world with no events,
allocation, writes, releases or resource/exit endings. This is nonvacuity
of a trusted specification, not native termination or observation coverage.

Public invocation fixtures permit distinct nonunit positive and negative
magnitudes, reject wrong signs, and admit identical/overlapping spans from
ready memory. Other controls cover count boundaries, a separately unreadable
second span, missing zero-count authority on either side, malformed bytes,
noncanonical counts and wrong ABI classes. The native probe checks signs
only: high unsigned bytes, an early difference opposite a later one, binary
zero before a difference, a difference exactly at the count boundary, live
one-past zero counts and overlap. Aligned 16-byte arrays exercise their
capability ends without relying on small-array padding. Finite probes do
not prove native satisfaction of these trusted contracts. Runtime axioms,
Machine semantics, interpreter registration and the validator are unchanged.

### Campaign 4 milestone 4t: bounded strncmp and early terminators

The trusted strncmp contract independently requires `bounded_length`
witnesses for both inputs, reusing strnlen's early-NUL domain rather than
memcmp's full-maximum span. This is the table's conservative B(a,n), B(b,n)
contract, not the weakest operational precondition: an immediate difference
does not waive an otherwise invalid bounded string on either side.

With bounded lengths left and right, the logical comparison window is
`min(n, min(left + 1, right + 1))`. It includes an earlier terminator but
never byte n. These additions are mathematical integers, not class-L
arithmetic that could wrap at SIZE_MAX. The window-bounds and readability
theorems prove that both source capabilities permit every compared byte,
with a well-formed byte domain. Total model memory and a result-existence
proof alone would not establish that authority obligation. Existing
readable-span extent results then apply under runtime readiness.

The result reuses memcmp's unsigned-byte order and arbitrary canonical
signed-int magnitude. Input-only premises construct a permitted invocation;
first-NUL uniqueness yields sign uniqueness, not result-word uniqueness.
The unchanged P/P/L-to-W ABI admits discarded results. Completions are pure:
exact memory/world, empty observations, no mutation, allocation, release or
resource/exit ending. No native termination or coverage is inferred.

Controls distinguish a shared NUL with different following bytes, an
earlier terminator versus a nonzero byte, huge bounds, exact-count
nonterminated spans, overlap, zero-count one-past authority and wrong signs.
Public invocations permit both signs with magnitude 512. Native probes
retain explicitly aligned allocation-end cases and check signs only.
Pinned strncmp also uses aligned/unaligned word loops and merged words;
the window is a logical dependency bound, not an exact native load trace.
These finite checks do not prove universal native satisfaction. Runtime
axioms, Machine semantics, registry, validator and site code are unchanged.

### Campaign 4 milestone 4u: unbounded strlen and the string bridge

The trusted `strlen_contract` returns the exact first-NUL offset as a
class-L size_t. `terminated_length` reuses `bounded_length` at SIZE_MAX,
requiring termination strictly before that sentinel. This is a logical
device, not a maximum-sized read: the input capability must cover only
the nonzero bytes and their NUL. Even an empty string needs one readable
live byte; a one-past pointer is not admitted.

The contract names a single object's identity/life and the byte interval
through the NUL as its read dependencies. `terminated_length_agree` proves
locality: preserving that identity's region lookup and those bytes keeps
the predicate true, regardless of other objects, bytes or auxiliary slots.
This supplies a footprint fact for a later derived Iris triple without
making the relational contract depend on Iris. All memory and the logical
world are preserved exactly; no writes, capability propagation, allocation,
release, observation, resource or exit outcome is authorized.

Input-only premises construct a permitted invocation, and every completion
returns the unique length of the original string. This proves specification
nonvacuity, not native termination. `StringLengths` bridges the predicate to
the existing checked list-string `c_string` under runtime readiness. The
forward direction constructs a finite list without readiness. The reverse
uses the existing freed-empty and address-space axioms to establish live
authority and a canonical length. Neither `c_string` nor puts is silently
strengthened on arbitrary model memories. The consumed-extent theorem
reuses the bounded-scan proof and includes the final NUL.

Public-call controls cover high bytes, unaligned starts, empty strings and
a final-byte NUL; reject incorrect lengths, absent in-object NULs, and
one-past/null/freed authority; and instantiate the bridge on the established
puts string. Native probes use an aligned 16-byte allocation with its sole
NUL at the last byte, checking full and interior lengths and the empty final
byte. The missing-NUL trap control remains. The pinned generic strlen aligns
its first word load downward and can load beyond the logical terminator:
these probes do not prove safety of every native load, universal contract
satisfaction, or which implementation the linked binary selects. Runtime
axioms, Machine semantics, existing call signatures and the registry are
unchanged.

### Campaign 4 milestone 4v: unbounded strcmp with independent strings

The trusted `strcmp_contract` requires independently terminated strings on
both inputs, even when their first bytes already differ. Its P/P-to-W ABI
has no count argument. `strcmp_result` compares unsigned bytes in the
mathematical window `min(left + 1, right + 1)`, including the earlier NUL.
The window is proved readable through both input capabilities by reusing
the bounded-string window theorem. Total model memory alone would not
justify those reads.

The comparison window is not the whole admission footprint: each input
depends on its referenced identity's region/life and its own bytes through
its own NUL. The longer string must remain valid beyond an earlier
terminator on the other side. Auxiliary slots are not input dependencies.
This is an explicit logical footprint for later Iris triples, not a native
load trace or a generic cross-memory frame rule. The call preserves all
memory and world exactly and permits no capability propagation, writes,
allocation, release, observations, resource endings or process exit.

Input-only premises construct a permitted invocation. First-NUL uniqueness
fixes the window and hence the signed result's sign, not its magnitude;
both signs permit canonical results with magnitude 512. Every represented
completion returns such an original-memory result. Nonvacuity does not
establish native execution, observation coverage or termination.

Public controls distinguish shared NULs with different following bytes,
strict prefixes in both directions, unsigned high-byte ordering, empty
strings, identical and overlapping spans, wrong signs, independently
unterminated inputs, one-past authority and wrong ABI shapes. Native rows
compare distinct equal aligned 16-byte arrays through their final-byte NULs,
including unaligned starts, then introduce a final nonzero-byte difference
and an earlier unsigned difference of the opposite sign. The pinned generic
strcmp uses aligned word loops and an unaligned second-pointer path that
aligns downward and merges words; loads before an argument or beyond the
logical dependency window remain implementation obligations, not something
these finite probes prove universally. Existing puts/invocation/machine
interfaces, runtime axioms, registry and validator remain unchanged.

### Campaign 4 milestone 4w: strchr and source-capability returns

The trusted `strchr_contract` admits a complete terminated string and a
canonical class-W int; its count-free ABI returns a class-P pointer.
`strchr_result` reuses first-match `memchr_result` over the string length
plus one, including the NUL. Strict termination proves this span readable
without runtime readiness. Input-only premises construct an actual pure
invocation, and every represented completion returns the unique exact
source-capability pointer or null. Searching any int whose low byte is
zero necessarily returns the terminating pointer, not null.

The identity-keyed read footprint is the source object's region/life and
all bytes through its NUL, even when an immediate match decides the result.
Auxiliary slots are not dependencies. The capability source `[mkSpan p 0]`
is deliberately separate: it permits copying p's own capability but cannot
import a capability from a complete auxiliary pointer slot and grants no
write permission. It is not a zero-byte read footprint or a maximum-sized
read. A hit retains Obj or Ro exactly; no ownership transfers and the result
is invalidated when its source object's lifetime ends. All memory and world
are preserved, with no observations, allocations, releases, resource or exit
endings. This relational interface remains independent of Iris.

Public-call controls distinguish a first repeated match from a later match,
null, capability amplification and capability loss. They cover 511 and the
canonical int representation of -1, 0 and 256 NUL searches, empty strings, Obj
as well as Ro sources, and a byte occurring only after the first NUL. Missing
termination, one-past/null/freed authority, noncanonical int words and wrong
ABI shapes fail admission. Native rows check high-byte int conversion,
aligned/interior searches through a final-byte NUL, empty strings and NUL
cut-off; the existing repeated-match and freed-result controls remain.

Pinned generic strchr delegates to strchrnul, whose initial word load
aligns downward and whose word scan can load beyond the logical dependency
interval. These finite probes do not prove universal native satisfaction,
which implementation is selected, or termination; libc remains trusted
behind this API contract. Existing call signatures and runtime axioms are
unchanged. The next separate slice is last-match `strrchr`.

### Campaign 4 milestone 4x: strrchr and last-match authority

The trusted `strrchr_contract` shares strchr's count-free P/W-to-P ABI,
canonical int admission and zero-size source-capability permission. Its
separate `strrchr_result` selects the last low-byte match in the mathematical
interval from zero through the first-NUL offset, or canonical null. A hit
must exclude later matches, not earlier ones. Complete terminated-string
admission independently proves readability of that entire interval.

Constructive nonvacuity uses finite-interval induction, without pretending
that shorter prefixes themselves satisfy terminated-string admission. The
proof constructs a returning invocation from input-only premises. Exact
pointer uniqueness, including the source capability, and pure invocation
extraction are proved. Low-byte-zero searches necessarily return the exact
terminator. Memory and world remain unchanged, with no observations,
allocation, release, resource or exit ending. No ownership transfers or
lifetimes are extended. The identity-keyed read dependencies remain the
source region/life and bytes through NUL, not auxiliary slots; the zero-size
propagation source is not a read footprint. These facts remain independent
of Iris, for later derived triples.

Public controls distinguish the last repeated match from the first and
reject null or correct-address capability substitution at a hit. They check
last high-byte matches after int conversion, NUL and empty inputs, bytes
before the argument or after its NUL, false hits at an admitted miss, and
retained Obj as well as Ro authority. Existing independent invalid-input
and shared-ABI controls apply unchanged. Native rows use a dedicated aligned
16-byte array with repeated high bytes and a final-byte NUL, including
interior starts and empty suffixes; separate cut-off controls exclude
matches past an earlier NUL in the same allocation.

Pinned generic strrchr delegates to memrchr over `strlen(s) + 1`, so both the
forward length scan and the reverse word scan are native obligations. The
reverse scan rounds its endpoint upward, loads backward and masks boundary
bytes; loads before the argument or beyond the logical interval remain
possible. The API proofs and finite probes do not establish universal native
satisfaction, implementation selection, coverage or termination. Runtime
axioms, existing call signatures, machine and registry are unchanged.

### Campaign 4 milestone 4y: memset's byte and auxiliary footprints

The first memory-writing slice is the additive trusted `memset_contract`:
P/W/L arguments, discarded or P return, canonical int and size_t, and
independent live writable destination authority. Positive counts additionally
require the referenced object's base to be divisible by eight. This is an
explicit conservative contract premise, not a new runtime axiom or a
destination-alignment requirement. The pinned runtime rounds auxiliary
offsets relative to the object base; without this premise a model object
at an unaligned base could disagree with absolute pointer-slot alignment.
Zero count does not require base alignment, but retains conservative live
Obj admission, including unaligned one-past pointers. Native memset returns
before checking any authority at zero count: rejected empty calls are
unmet contract obligations, not claims of native traps.

The exact byte footprint is the requested half-open interval. The separate
auxiliary footprint contains every eight-aligned slot whose eight-byte
interval intersects that nonempty byte interval. A one-byte fill can thus
clear a slot starting before the destination. Completions repeat the low
byte, clear these slots, preserve every other byte and auxiliary entry, and
leave all regions and the world unchanged. Every accepted prefix has the
same outside-footprint frame. Returning the exact destination pointer uses
only its own capability, with no ownership transfer, allocation, release,
resource ending or event. Existing string contracts and runtime axioms stay
unchanged for Campaign 3's derived Iris triples.

The internal permission root rounds only the start down to include the
preceding auxiliary slot. Its end stays at the byte endpoint: authority is
needed for slot starts, not all bytes in the last pointer word. Ordinary
writable-byte admission and base alignment prove this root writable; the
prefix frame still forbids modifying the extra preceding raw bytes. The
result constructs a local effect and an actual returning invocation from
input-only premises. The existing preservation theorems then retain runtime
readiness and identities. This is logical nonvacuity, not libc execution.

Public controls cover repeated-byte conversion rather than little-endian
integer storage, partial and crossing slots, exact endpoints, preserved
byte/capability neighbours, zero count, exact pointer returns, independent
scalar/ABI failures, and the otherwise-writable unaligned-base counterexample.
Native probes write back a pointer's unchanged last byte before testing loss
of usable authority, while separate controls preserve neighbouring pointers,
test an exact word boundary, and check zero-length and converted-byte fills.

This exact logical frame is not yet a complete native instance. In particular,
large memset paths exit and re-enter Fil-C during byte writes and auxiliary
clearing: the collector may rewrite unrelated capabilities to freed objects
at those internal safepoints. Universal native prefix/completion coverage,
that collector relation, and termination remain open; finite probes do not
establish them. Do not widen writable roots to conceal those rewrites.
The next separate slices are copying and fresh-allocation contracts, with
partial-pointer smidgens/boxing requiring their own reviewed relation.

### Campaign 4 milestone 4z: snapshot memcpy, mempcpy and memmove

The next additive contracts share one snapshot byte/auxiliary relation.
`memcpy_contract` and `mempcpy_contract` require byte nonoverlap;
`memmove_contract` permits overlap in either direction. All use independent
readable source and writable destination authority, canonical size_t, and
positive-count alignment of both object bases. Operand addresses can be
unaligned. Empty calls conservatively require live capabilities, as before.
memcpy and memmove return the exact destination; mempcpy returns its
mathematical endpoint with the same capability. Readiness proves that
endpoint in-object or one-past and below the address-space wrap boundary.

Each destination byte comes from the original source snapshot. Each touched
auxiliary word retains the original translated source capability only when
the entire word was copied and its source is aligned; partial endpoint
smidgens and out-of-phase words become CNone. Thus fragments do not compose
authority. Even a partial self-copy may clear metadata without changing
address bits. Byte-disjoint adjacent ranges may share a touched auxiliary
word, so hull disjointness is not required. An original complete-slot read
proves capability availability; no new capability constructor, authority
rule or runtime axiom is needed. The destination-only permission hull and
exact prefix frame are those of the preceding memset milestone.

Any specified result is proved a local effect, and independent inputs
construct an actual invocation. Extraction constrains every completion.
Ready positive fixtures and public controls distinguish both overlap
directions, exact Ro/Obj propagation, partial/self/out-of-phase copies,
CNone overwrites, adjacent byte ranges, neighbours, zero count and the
one-past mempcpy return. Native pointer-array moves, unchanged-bit fragment
copies and byte-buffer phase controls supply finite evidence.

The reviewed partial-word relation does not establish universal native
satisfaction. Even small copies may allocate auxiliary storage, exit,
collect and reload a stored capability. Internal metadata-allocation
failure, those collector prefixes, and lower/box representation
correspondence remain open; this logical contract admits only its selected
returning effects. Do not model that storage as caller-owned allocation.
String copies must not inherit this auxiliary guarantee merely because
their byte result is a terminated copy: the selected implementation's stores
need a separate specification. Fresh allocation is next for the Iris
slot-buffer proof, followed by that string-copy and strdup boundary.

### The next milestones, in order

1. **Close `hi.c`.** Install concrete startup/stdio representation and
   request contracts; model main's return, flush and `exit`/handlers as
   events, plus blocking/divergence and resource endings. Require
   external-symbol coverage and admissibility at every reached call,
   independently of whether it has an `invoke` derivation. An empty
   relation must never prove safety by deleting an invalid execution.
   Link the pinned modules and prove adequacy before claiming
   `never_panics`; no such claim is made by the abstract integration.
2. **Grow by Hello contract kinds.** Add bounded byte/string operations,
   fresh allocations and owned release, then formatting, argv/environment,
   locale/conversion, opaque streams/descriptors and callbacks, following
   the native table. Connect Prolog/extraction and native observations;
   only then restate and validate `opt:refines/2` as trace inclusion.

## Campaign 5: static discharge by certificate

Goal: a new evidence form in the checked IR, `discharged(Cert)`, that
replaces a check whose failure a certificate proves impossible, with
the certificate checked reflectively in Rocq and found by Prolog.

This is the payoff of uncatchable traps: a check is a pure assertion, so
one that cannot fail is dead code and its removal is exact. It
generalizes what `span_test` with `renew_if` and `limit` with
`check_limit` already do by pattern: a runtime test at a boundary
establishes a precondition, and a proof carries it through the code. The
certificate language is what makes the set of accepted shapes
open-ended instead of hand-blessed. The term grammar of
[ir.pl](../src/ir.pl) is the contract between frontend, interpreter and
backends, so `discharged(Cert)` enters it only with the orchestrating
thread's agreement and a reviewed validator, interpreter and emitter
contract.

The mechanism, in three parts:

- **A checker in Gallina.** `discharge_ok : func -> cert -> bool`,
  proved sound once: `discharge_ok f c = true` implies the check `c`
  names cannot fail on any execution of `f` under its preconditions.
  Per-module proofs are then `apply discharge_sound; vm_compute;
  reflexivity`, so proof size does not grow with program size and no
  per-program tactic work is needed.
- **A certificate language.** First version: for each loop header, an
  interval invariant on the affine index temporaries, plus the runtime
  fact it rests on (a `span_test` or `limit` that dominates the loop, or
  a parameter the caller checked). The checker verifies that the
  invariant is inductive and that each discharged access's range lies
  inside the guarded span. Later versions add facts across pointer loads
  and through phis, in the same shape as forward reuse
  ([forward.md](forward.md)).
- **A finder in Prolog.** CLP(FD) over the loop's index arithmetic,
  widening to intervals, emits the certificate. It is untrusted. When it
  finds nothing, the check stays; nothing is ever weakened.

Where the free flag is at stake (the temporal half), the certificate
does not try: the access becomes a `renew` with bounds discharged and
the flag retested, which is cheap. Proving absence of free needs
ownership reasoning and is an inquiry, not this campaign.

The behavior-preservation side is free: the trace of a module with a
discharged check equals the trace with it, because the check was the
identity on every execution. State that as one lemma against
Campaign 4's semantics so the `--checks` refinement obligation is met by
construction.

Gates: the Lua benchmark compiled with `--checks=discharge` passes the
native suite, the extracted checker accepts every certificate nanofil
emits, and a deliberately wrong certificate (off by one in the
invariant) is rejected by the checker and by nothing else. Measure the
cycle savings against Campaign 0's histogram; if the discharged class
was cheap, say so. The checker's soundness proof builds on Campaign 3's
lemmas; the finder grows one invariant shape at a time.

## Campaign 6: integration

Goal: the extracted checker is a Nix check in Filnix, the playground
explains each discharged obligation from the certificate, and nothing in
a routine build asks a model whether evidence is convincing.

- **The gate.** A derivation `nanofil-check` that takes a module's
  checked IR and certificate and runs the extracted OCaml checker,
  beside today's checks in [nix/check.nix](../nix/check.nix) and the
  Lua build in [nix/lua.nix](../nix/lua.nix). `nanofil cc`
  with `--checks=discharge` fails the build if the gate rejects. The
  Prolog validator still runs first as the producer's self-check, so a
  disagreement between the two is a test failure, never a silent
  acceptance.
- **Pinning.** The certificate names the semantics version, the checker
  version and the runtime axioms commit. Filnix's Fil-C bump is the
  moment to re-run Campaign 2's native axiom tests.
- **Explanation.** The playground already shows each pass's real
  intermediate IR. A discharged check shows its certificate: the
  invariant, the runtime fact it rests on, the source line via
  provenance. [campaign.md](campaign.md) asks that this view read the
  compiler's result rather than reconstruct a second analysis; the
  certificate is exactly that result.
- **Drift control.** [tests/guide.sh](../tests/guide.sh) recomputes
  every documented IR block, and this page is drawn by dterm beside the
  modules, so a predicate it names that disappears fails the site build;
  the same mechanism should recompute the Rocq-side examples, so the
  formal docs cannot go stale against the compiler either.

Gates: a Filnix build of the Lua package through nanofil passes the
gate; removing one line from a certificate fails the gate; the
playground renders the certificate for the `sum` example in
[the README](../README.md#a-look).

## Campaign 7: a program that never panics

Goal: for one pinned program, ideally a whole Nix closure, a theorem
that no Fil-C check of it ever fails on any input its entry contract
allows. When Filip Pizlo says a Fil-C program panics, he means a Fil-C
check failed: a trap on a capability violation, or on some other
operation that would be a memory safety error without Fil-C's checks.
"This program never panics" is then memory safety of that program with
respect to Fil-C's capability semantics.

There is no general version. Programs with memory errors exist, are
valid, and panic; that is Fil-C working. So this is a theorem per
program, and its unit is a derivation: every object of the program and
of the libraries it links, compiled by a pinned nanofil with pinned
flags, against a pinned runtime. Examples: `ls`, and as the stretch,
this build of OpenSSH's server.

### What counts as a panic

In the model's terms (Semantics.v's `outcome`, interp.pl's outcomes),
the property sorts every way a run can end:

| How a run ends | interp.pl | Counts as | Why |
| --- | --- | --- | --- |
| `Trap r`, r one of `NullCapability`, `OutOfBounds`, `Misaligned`, `Readonly`, `NotAFunction`, `ArgumentSize`, `ReturnSize`, `InvalidFree`, `DoubleFree` | `trap(Reason)` | a panic | a capability check failed: without Fil-C, a memory safety error |
| `Trap (Early r)` | `trap(early(R))` | a panic | a `check_ahead` trapped early on a failure the run was going to reach |
| `Unchecked r` | `unchecked(Reason)` | impossible | soundness of checking: never, in a valid module |
| `Trap OutOfMemory` | `trap(out_of_memory)` | not a panic | the runtime refused an allocation it cannot hold; any runtime may (Runtime.v), so no program could be proved free of it |
| `Trap TooBig` | `trap(too_big)` | not a panic | a request over 2^48 - 1 bytes, which C's `malloc` would answer with null; natively a "filc safety error", but not a memory error |
| a stack overflow | native only | not a panic | a resource limit, like out of memory; the model has no stack bound |
| `exit`, `abort` | external calls (Campaign 4) | not a panic | the program chose to stop |
| `Ret`, `Rets`, `RetVoid` | `ret(V)`, `rets(Xs)`, `ret` | not a panic | |
| a run that never ends, or `OutOfFuel` | `out_of_fuel` | not a panic | the property speaks of every state a run reaches, so divergence is allowed and fuel plays no part |
| `UB r` | `ub(float_conversion)` | ruled out | the model gives no continuation after it, so nothing can be proved about what follows |
| `Unreachable` | `unreachable` | ruled out | natively a crash (`ud2`), not a Fil-C check, and never a correct program's ending |
| stuck | instantiation error | ruled out | the run left the model: an external call with no contract, or code outside the subset |

The panic rows follow Filip's meaning. The rest are mbrock's decisions
(November 2026), listed at the end of this campaign.

### The statement

Over Machine.v's machine, for a program P (the linked checked IR of
the closure, its initial memory and its entry function):

```
never_panics P :=
  forall (R : Runtime), R.ready R.start (initial memory of P) ->
  forall input, well_formed_entry input ->
  forall environment the contracts of P's external calls allow,
  forall st, mreachable ge (start P input, R.start) st ->
    ~ ends_in_failure st
```

where `ends_in_failure` is a step to `Done (Trap r)` with r a panic
reason, `Done (Unchecked _)`, `Done (UB _)`, `Done Unreachable`, or
`Stuck`. Quantifying over every runtime means the proof may not depend
on where objects are placed or on when the runtime refuses an
allocation; quantifying over every state reached rather than over
outcomes makes divergence harmless. Readiness of the initial memory is
a fact about P's data for any runtime that starts the heap above it,
the planned fix in [rocq.md](rocq.md); until then it is a hypothesis
here as in Campaign 3.

### How it builds on soundness of checking

- **`Unchecked` is excluded for free.** Every module of the closure is
  valid, so `valid_no_unchecked` rules out the one outcome whose native
  meaning is unknown. What is left are explicit points of the IR: each
  `check` and reuse form's retest, each `free`, each function check and
  each varargs or external-call precondition. Never panics is the claim
  that none of them fails: every check site discharged, in Campaign 5's
  sense, across the whole closure. Allocation refusal is not an
  obligation, as the panic table above specifies.
- **The proof may take the compiled IR as it is.** A reused or renewed
  check stands for the original one only because soundness of checking
  says the evidence is real; without Campaign 3, a proof about the
  optimized IR would say nothing about the accesses it no longer checks.
- **Or the simplest IR of the closure.** With Campaign 4's refinement
  (trace inclusion, trapping earlier only where the original would
  trap), a program that never panics and never reaches UB has only
  refinements that never panic, so the proof may target the IR before
  the middle end and carry over to every `-O` and `--checks` mode.

### Against Campaigns 4 to 6

- **Campaign 4** makes a program a closed thing. Without contracts a run
  is stuck at its first external call, so the statement is about
  nothing. The entry contract (what `argv` and the environment may be)
  and the contracts of `read`, `write`, `opendir` and the rest are its
  hypotheses, and `exit` is an event.
- **Campaign 5** supplies the evidence: a never-panics proof is a
  discharge certificate for every check site, but with preconditions
  that flow across calls and through the whole closure, where
  Campaign 5 starts within a function. It also needs the temporal half
  that Campaign 5 leaves to `renew`: never panics means no use after
  free, no double free and no invalid free, so the temporal-discharge
  inquiry is a prerequisite here, not an option.
- **Campaign 6** supplies the pinning. The certificate names the
  closure's derivation, the nanofil and checker versions, the runtime
  axioms' Fil-C commit and the contract table; a Nix check rebuilds the
  closure and replays the certificate. A Fil-C bump reruns the axiom
  tests before any certificate is trusted again.

### Outside the proof

- **libc and anything filcc compiled.** Their code is not in the model.
  Their contracts say what they need and promise, and that they never
  panic when their callers meet those needs is trusted. The
  libc-inside-the-model and filcc translation-validation inquiries
  shrink that trust.
- **The native binary.** The theorem is about the model. Implementation
  correctness (the third claim) carries it to native code: native
  difftests, and the runtime's own correctness.
- **Threads and signals.** The model has one thread and no signal
  handler: installing a handler or starting a thread is a call to an
  external with no contract, which ends the run as a failure, so a
  program that does either needs its handler verified as program code.
  Another thread's free shows at any check
  natively (runtime-axioms.md), which is the concurrency inquiry.

### Worked first target: GNU Hello

The proof below is still a sketch; [step 0's census](trap-census.md) is
now measured, with a reproducible query. GNU Hello is the right first
closure: [nix/hello.nix](../nix/hello.nix) already
builds it with every object compiled by nanofil, once per configuration
(`plain`, `O`, `O-reuse` and the rest), and checks it against filcc's
build. So the pinned unit exists: the derivation `nanofil-hello-O`, which
fixes Hello 2.12.3's source, its gnulib, nanofil's commit, the flags,
and the Fil-C glibc and runtime it links. A smaller step comes first,
`hi.c`: `int main(void) { puts("hello"); return 0; }`. It is
compiled by nanofil and links the same libc, and has one libc call, no
input and no free. Hello is the same proof with more contracts, a real
entry contract, the heap, and a loop over strings.

#### What Hello asks of libc

The original sketch said 66 libc symbols. At this pin, `nm -D` of
nixpkgs' hello-2.12.3 instead gives 61 GLIBC symbols plus three non-libc
weak hooks. The actual nanofil build has 56 distinct libc names after
normalizing its ABI prefixes and startup duplicates. The
[census](trap-census.md) lists all 61 stock names by contract kind and
the exact delta for nanofil. These are requirements for trusted,
natively probed contracts, not contracts already proved. The broad
kinds are:

| Kind | Hello's calls | What the contract says |
| --- | --- | --- |
| Memory functions | `strlen`, `strnlen`, `strchr`, `strrchr`, `strcmp`, `strncmp`, `memchr`, `memcmp`, `memcpy`, `memset`, `strdup` | Each requires capabilities that cover what it reads or writes: a readable object that holds a NUL within bounds, or n bytes in bounds. Under Fil-C, an unterminated string traps inside `strlen`, so the panic belongs to the caller, and its precondition is an obligation at the call site. |
| Allocation | `malloc`, `calloc`, `realloc`, `free` | Allocation is the runtime's `alloc`. It may return null and is never a panic. `free` requires null or a live heap base. |
| Formatted output | `__printf_chk`, `__fprintf_chk`, `__sprintf_chk`, `fputs`, `fputc`, `error` | The varargs must match the format string (Fil-C checks every `va_arg`). Stream acceptance is distinct from later device delivery; buffered success does not imply a `write(fd, bytes)` event. |
| Arguments and locale | `getopt_long`, `optarg`, `optind`, `setlocale`, `nl_langinfo`, `bindtextdomain`, `textdomain`, `dcgettext`, `__ctype_b_loc`, `mbrtowc`, `mbrtoc32`, `mbsinit`, `iswprint`, `iconv*` | `getopt_long` needs the entry contract's `argv` and a long-options table that ends in a zero entry. It returns pointers into `argv`. `__ctype_b_loc` returns a table indexed from −128 to 255, a classic out-of-bounds risk. The locale functions return strings whose lifetimes the contract must state. |
| Ending | `exit`, `_exit`, `abort`, `__cxa_atexit`, `close_stdout` through `ferror`, `fclose`, `__fpending` | `exit` is an event and the end of the trace. Handlers registered with `atexit` run during `exit`, so they are part of the program's proof. |

#### The proof, layer by layer

1. **Semantics (Campaign 4).** The labelled
   [ExternalMachine.v](../rocq/theories/ExternalMachine.v) extension
   executes admitted direct contract calls and preserves Campaign 3's
   invariants. Failed caller obligations are explicit specification
   failures, not necessarily native Fil-C traps. Buffered stream
   acceptance is distinct from kernel `write`; flush and `exit` need
   their own contracts. The extracted driver still uses the old core,
   whose `external_call` models only `free`. Native contract instances,
   prefix coverage and whole-program adequacy remain open.
2. **Linking.** One genv holds the functions and data of every
   translation unit in Hello's closure, with libc's symbols resolved to
   contracts. The model now runs one module.
3. **The environment.** The entry contract describes the starting
   state: `argc ≥ 1`, and `argv` and `envp` as arrays of readable,
   NUL-terminated strings, each array ending in null. These are
   quantified over every content and length: Hello's `--greeting=` takes
   any string. The locale is whatever `LC_ALL` names; quantifying over
   it makes `setlocale`'s result one more input.
4. **A program logic over Machine.** It uses triples
   `{P} f {Q}` per function, with capabilities as resources: an object,
   its region and flags, and its bytes. It has a rule for each
   instruction, a call rule that uses callee triples and libc contracts,
   and loop invariants. Its adequacy theorem connects the logic to runs:
   if main's triple holds under the contracts, no state reached by
   `mreachable` ends in failure. Adequacy must hold for every `Runtime`,
   so the logic may not assume where objects are placed.
5. **Per-function triples for Hello's own code.** These cover `main`,
   gnulib's `quotearg`, `version_etc`, the `xalloc` family,
   `close_stdout`, and the rest. Most specs are about strings: "a
   readable object with a NUL at or after offset 0". The heap ones
   (`quotearg`'s slot vector, grown with `realloc`) need temporal
   reasoning: no free between a pointer's creation and its use.
6. **Composition.** The final statement is `never_panics` of
   `nanofil-hello-O`: valid modules, starting ready, the entry contract,
   and main's triple with an empty postcondition.

#### What exists and what is missing

| Piece | State | Where |
| --- | --- | --- |
| `Unchecked` excluded for every valid module | exists for the core subset (Campaign 3), for every runtime, given a ready start | [Soundness.v](../rocq/theories/Soundness.v)'s `valid_no_unchecked`, assembled from Chain.v's `run_access_checked`, Renew.v's `run_reuse_checked`, Guard.v's `run_guard_checked` and Doomed.v's `run_doomed_checked`; `interp_valid_no_unchecked` is closed, an instance; `spares`, once a hypothesis, is a lemma for every runtime (`spares_any`) |
| The exact condition under which an access traps | exists | [Memory.v](../rocq/theories/Memory.v)'s `cap_access_res`; [Coverage.v](../rocq/theories/Coverage.v)'s `cap_access_covered` and `covered_access_checked`. A check site's obligation is "`cap_access_res` does not trap", a decidable predicate |
| Validator facts hold in every reached state | exists for the base forms | [Evidence.v](../rocq/theories/Evidence.v)'s `evidence_after_holds` and `entry_holds`, Persistence.v's `mreachable_inv`. A triple may use them as known facts instead of proving them again |
| Runs over any runtime: fresh allocation, frees, retention, safepoints | exists | [Runtime.v](../rocq/theories/Runtime.v)'s ten axioms, [Machine.v](../rocq/theories/Machine.v)'s `mreachable_ready`, `mstep_refines` and `kept`. These supply the allocation and free rules of the logic. `free_res_lifetime` is what makes a use after free a trap and not a silent read |
| Which trap reasons are panics | stated here | the table above; `alloc_res`'s `too_big`/`out_of_memory` split in [Ops.v](../rocq/theories/Ops.v) already separates refusals from errors |
| Running Hello's IR in the model to test contracts | missing | the extracted model and `agree.sh` exist, but externals are stuck |
| Initial readiness for every runtime | hypothesis | the heap starting above the data ([rocq.md](rocq.md)) |
| External-call step, events, contract language | abstract direct-call integration and finite labelled runs exist; native/executable integration missing | Campaign 4's [ExternalCalls.v](../rocq/theories/ExternalCalls.v) and [ExternalMachine.v](../rocq/theories/ExternalMachine.v), starting with `puts` |
| Linking several modules | missing | Run.v takes one module |
| Program logic and adequacy | in the model, on Iris (mbrock's decision, 2026-11-09) | [Language.v](../rocq/theories/Language.v): an `ectxi_language` whose context is the callers stack, with adequacy (`wp_never_panics`); [Heap.v](../rocq/theories/Heap.v) and [Logic.v](../rocq/theories/Logic.v): the ghost heap and a weakest-precondition rule per instruction; the list sum's triple is the first example ([logic.md](logic.md)) |
| libc contract table | trusted native specification and nine probes exist; Rocq starts with `puts` | [libc-contracts.md](libc-contracts.md): 56 Hello names, `puts` and `fcntl`; not a proof of libc |
| Hello inside the model's subset | measured: all 178 functions in 81 objects inside; every object `Some true` | [step 0](trap-census.md) calls the extracted Validate.v `valid` directly; no `None` or `Some false`; this is not execution through the still-missing libc contracts |

#### Where the per-function obligations come from

A never-panics proof discharges a finite list of sites per function,
read from the pinned checked IR:

- **Residual checks.** Each class-`a` site still in the checked IR
  after `-O --checks=combined`, counted as Campaign 0 counted Lua's
  ([residual.md](residual.md)). The same query, run over Hello's
  translation units, is the obligation census. Its shape classes predict
  the cost: static-bounds globals and affine loops are discharged by
  Campaign 5's certificates, and pointer chasing needs a triple.
- **Reuse retests.** A `renew`, `half` or hull form reduces its site's
  obligation to the parts it tests again. Flag-only renewals (24.49% of
  Lua's) are purely temporal: no free since the check, and not
  read-only.
- **Frees.** Every `free` and libc `free` call: null, or a live heap base
  not yet freed.
- **Calls through pointers.** The function check: a function, of the
  right signature (`NotAFunction`, `ArgumentSize`, `ReturnSize`).
- **Varargs.** Each `va_arg` in Hello's own variadic functions and each
  variadic libc call: the arguments match (`ArgumentSize`).
- **libc preconditions.** Each external call site: the contract's
  precondition from the table above.
- **Allocation sites** are not obligations: refusing is the runtime's
  choice.

The census is mechanical and needs no proof, so it is the first
deliverable. Its size and shape classes for `hi.c` and Hello decide how
much a per-function triple must carry and how much Campaign 5 can
discharge.

### The quest, in steps

| Step | Program | Needs |
| --- | --- | --- |
| 0 | [measured: obligation census](trap-census.md) of `hi.c` and `nanofil-hello-O`, plus `valid` over all Hello objects | Campaign 0's query over Hello; no proof |
| 1 | proved: [rocq/programs/sum.c](../rocq/programs/sum.c), a loop over a read-only global array with no input and no external call ([Sum.v](../rocq/theories/Sum.v)), and [rocq/programs/prefix.c](../rocq/programs/prefix.c), the same loop stopped by an `int` input n, for every n ([Prefix.v](../rocq/theories/Prefix.v)) | `never_panics` stated in Rocq ([Panics.v](../rocq/theories/Panics.v)); the modules as fixtures ([rocq/programs.sh](../rocq/programs.sh)); computed runs checked step by step over abstract memory; for a loop with no small bound, [rocq/programs/cycle.c](../rocq/programs/cycle.c), an assertion at each point and one symbolically computed step from it ([Cycle.v](../rocq/theories/Cycle.v), [Symbolic.v](../rocq/theories/Symbolic.v)); for a heap object, [rocq/programs/buffer.c](../rocq/programs/buffer.c), the same with no premise, since no safepoint frees it (`collector_live`; [Buffer.v](../rocq/theories/Buffer.v)) |
| 2 | `hi.c`, built by nanofil against the pinned libc | the external-call step; contracts for `puts` and the `exit` path; linking |
| 3 | GNU Hello, `nanofil-hello-O` | the entry contract; about 60 libc contracts; triples for gnulib's string code; temporal reasoning for `quotearg` |
| 4 | `ls`, from [nix/coreutils.nix](../nix/coreutils.nix) | contracts for directories, `stat` and locale; a malloc-heavy program |
| stretch | this build of OpenSSH's server | its crypto libraries inside the closure; `fork`, signals and privilege separation; the concurrency inquiry |

How step 1 is proved. nanofil -O's checked module of sum.c is
committed as a Gallina term (SumCode.v), and the quick Rocq check fails
when nanofil no longer makes it ([rocq/programs.sh](../rocq/programs.sh)).
The program has one path, so Sum.v computes it with the model's own
`step` on the initial memory (59 states) and then checks each step
again with the memory and fuel abstract: every state steps to the next,
returns 10, or runs out of fuel, in any memory that agrees with the
initial one on the array's bytes and region. Runtime.v's safepoint
axioms keep that agreement, since the array is global data, which no
free empties, and no byte moves. The theorem needs neither readiness
nor `spares`, and `Print Assumptions` of the interpreter's instance is
empty. Changing the loop to `i <= 4` makes both the fixture check and
the proof fail.

With an input, prefix.c's loop compares its index with n at each
iteration, and only the comparison with 4 guards the access. Prefix.v
does not reason about n's value: at each comparison with n it allows
both answers. That gives six runs (n from 0 to 5); run 5 stands for
every other run until that run leaves the loop, and each other run adds
five states of its own. Every state is checked with n left as a
variable in the environment. The input is a 32-bit word, as the ABI
passes an `int`. Changing the guard to `i <= 4` fails the proof at run
5, which then reads past the array.

A loop the input runs any number of times has no list of runs.
cycle.c sums `xs[i % 4]` for i from 0 while i < n, so n up to 2^31 - 1
iterations. Cycle.v proves it by Floyd's method: an assertion at each of
the function's 19 points says which temporaries hold which words, with
an integer range for each (the loop's index is between 0 and 2^31 - 1,
`i % 4` between 0 and 3, the checked pointer inside the array), and
`cycle_safe` shows that one `step` from any configuration satisfying an
assertion is safe and reaches a point whose assertion holds. The step is
computed by Symbolic.v's `compute_step` with the environment, memory and
fuel abstract: `cbn` reduces it, the assertion's facts are rewritten in
where it gets stuck, `lia` decides the integer comparisons the access
check and the class wraps make, and a comparison the facts leave open
(the one with n) is split into its two answers. Panics.v's
`never_panics_by_invariant` is the proof rule: an invariant that holds
at every admissible start, that every step keeps without failing, and
that a due safepoint keeps gives `never_panics`. Cycle.v compiles in
about 20 s, against Prefix.v's 66 s, and its cost grows with the
function's size, not with the trip count. Changing the loop to
`i <= n` (i wraps to negative at INT_MAX) or the index to `i % 5` fails
the proof.

A heap object adds two things, both in Buffer.v. buffer.c allocates
four longs (`__builtin_alloca`, which Fil-C places in the collected
heap), fills them, then sums `p[i % 4]` as cycle.c does. First, the run
chooses the object's base: the proof rule now hands the invariant every
base that is `fresh` in the current memory (the runtime's
`fresh_allocation` gives that where it is ready), and the assertions
speak of any such base b: `v4` holds a pointer to b with b's capability,
and b's region is a live heap object of 32 bytes. Second, a safepoint
must leave the object alone. The theorem first took a premise for that,
`safepoint_keeps_live`, because Runtime.v's safepoint also stood for
signal handlers and could free a live heap object. A handler is the
program's code, not the runtime's, and the collector frees nothing, so
the axiom became `collector_live` (no region changes at a safepoint)
and `buffer_never_panics` holds for every runtime with no premise. Changing the fill loop to `i <= 4` (a write past the buffer)
or the read to `p[i % 5]` fails the proof.

Compile time stays proportional to the function: Buffer.v's 32 points
take about 35 s, Cycle.v's 19 about 20 s. Two choices in Symbolic.v
keep it so: the function is kept abstract and each block is computed
once (`block_fact`), and each wrap and comparison is tried once,
innermost first: a wrap that arithmetic cannot drop becomes an unknown
in its range, and a comparison it cannot decide is split at once.

Buffer.v is the last proof with one invariant for the whole program. A
second function or object means rewriting that invariant, so the next
step is a program logic whose facts travel with ownership of objects by
identity, with one adequacy theorem into `never_panics`: the brief,
with an assessment of the Iris proposal, is [logic.md](logic.md).

Gates: each step's proof is checked in a Nix check, and its
certificates are replayed by the extracted checker. A planted
off-by-one in the program makes the proof fail and a native run panic.
Nothing in the build asks a model.

Decisions (mbrock, November 2026):

- **`too_big` is not a panic.** It is a refusal, like `out_of_memory`:
  no memory is touched, and C's `malloc` would answer with null.
- **A stack overflow is not a panic.** It is a resource limit, and the
  model keeps no stack bound.
- **`UB` and `unreachable` are ruled out.** The theorem also proves that
  neither happens: the model has no continuation after `UB`, and
  `unreachable` is natively a crash that no Fil-C check catches.
- **The entry contract is any input:** every well-formed `argv` and
  environment, not a precondition stated per program.
- **libc stays trusted behind contracts,** each probed by a native test
  as the runtime axioms are. Compiling it into the closure with nanofil
  remains the libc-inside-the-model inquiry.

## Inquiries and investigations

Questions the campaigns will force, or that could redirect them. None is
scheduled; each has a cheap first step.

| Inquiry | Question | First step | Could change |
| --- | --- | --- | --- |
| Integer-to-pointer | What capability does `itop` yield, and when does laundering recover one? nanofil ([launder.pl](../src/launder.pl)) and filcc (`inferPointerAsIntLaundering`) each encode an answer; the model must state one | Write the rule as a Gallina definition and diff the two implementations on the corpus | Which programs trap; Campaign 1's value model |
| Pointer `cas` | It compares addresses only and ignores capabilities, so an ABA on capabilities passes; why is that sound? | State the argument in one lemma (the access check still runs on the loaded pair) | Whether atomics enter the core subset |
| Intrinsic typing | Make `a` and `f` dependent types indexed by pointer, range and an epoch bumped at every safepoint, so coverage and persistence are typing, not a theorem | Prototype in Agda or Rocq on the `sum` example; compare proof effort with Campaign 3's extrinsic route | Campaign 3's whole shape |
| Temporal discharge | Proving no free between a check and a later access for heap objects needs ownership; is Iris worth instantiating for the IR? | Count how many Campaign 0 residual checks are flag-only after `renew`; if few, skip | Decided 2026-11-09: Iris is instantiated (Language.v, Logic.v), and live tokens discharge the temporal half |
| Capability erasure | A pointer whose every use is proven could live as a raw address inside a region; interfaces stay fat | Define erasure for a single function with no stores of the pointer; measure on the benchmark | A second performance tier beyond check removal |
| Concurrency model | The model is one thread's (mbrock's decision, November 2026). A free-at-safepoint event is not enough for threaded programs: another thread's free shows at any check natively (tests/c/prog/axiom-threads.c). What would state the theorem for them? | A free event allowed before any instruction, emptying only a live heap object's bounds; run theorems weakened to "checked, or freed since its check"; re-check Campaign 3 | Campaign 2's axioms; Campaign 4's traces |
| libc inside the model | Compile musl (or Fil-C's libc) with nanofil, moving libc from axioms into the theorem | Survey which libc functions the corpus needs and whether nanofil's C subset covers them ([survey.md](survey.md)) | Campaign 4's trusted base |
| filcc translation validation | Map FilPizlonator's LLVM output into checked IR and run it through the same checker | Hand-translate one function's filcc output; list the vocabulary gaps | Reach: every package in Filnix, not only nanofil's |
| Floats | [ieee.pl](../src/ieee.pl), an integer-only model, is transcribed as Ieee.v and in the core subset; prove it against a reference? | Differential-test the extracted version against a reference IEEE implementation | Whether float results carry a proof, not only agreement |
| Backend fusion | The check-plus-access templates are a closed set; validate instruction selection for them only | Enumerate the templates and write a native trace oracle before considering any x86 model | How much of claim 3 gets any evidence |

## Non-goals and things to resist

- **An end-to-end compiler proof.** [campaign.md](campaign.md) already
  says it is not a prerequisite; it stays that way. Claim 3 gets native
  oracles, not Rocq.
- **Modeling x86-64.** The backend's fusion templates are a closed set;
  a trace oracle gives most of the assurance for a fraction of the cost.
- **Porting nanofil to a proof assistant.** Prolog remains the compiler.
  Rocq checks evidence; it does not compile.
- **Interaction trees in the core.** Revisit only when Campaign 4's
  contracts make compositional handlers worth their coinduction.
- **A general optimizer framework.** Certificates extend evidence, not
  the middle end. Broad arithmetic optimization is not on this path.
- **Postulates.** No `Admitted`, no `Axiom` outside the Campaign 2
  module type, no annotation in C source that manufactures authority. An
  obligation nobody discharged stays a runtime check.
- **Letting the model become the gate.** AI-found invariants are
  evidence producers; a deterministic checker replays them. A build
  never asks a model whether a proof is convincing.

## Working method

- **Transcribe before designing.** Campaign 1 copies the interpreter's
  choices; a disagreement between Gallina and Prolog is a fixture, and
  the Prolog is presumed right until the native tests say otherwise.
- **Every theorem has a counterexample test first.** Before a rule is
  proved, a native or symbolic test shows what breaks when it is wrong:
  alias frees, wrong allocation identity, misalignment, rights, helper
  exits, moved traps. Campaign 2's axiom probes are the pattern.
- **Fail-first on behavior change, byte-identical on refactor.**
  Unchanged from [campaign.md](campaign.md): snapshot gates for
  refactors, a failing test before every semantic change.
- **Report what became clearer.** Each campaign ends with a `docs/` note
  saying what the model clarified, where it still differs from the
  compiler, and which inquiry it opened or closed. Line counts and proof
  sizes are symptoms, not goals.
- **Pin everything a certificate depends on.** Semantics version,
  checker version, runtime commit, libc contract table. A certificate
  that does not name them is not a certificate.

## Reading list and prior art

In the order the campaigns need them.

- **CompCert's memory model** (Leroy and Blazy, JAR 2008; the v2
  revision with Appel and Stewart). Blocks, offsets, permissions, memory
  injections. The capability model here is simpler, but the
  partial-operation discipline and the injection technique for pass
  proofs carry over directly.
- **Vellvm** (Zakowski, Beck et al., ICFP 2021). LLVM IR semantics in
  Rocq via interaction trees; externals as uninterpreted events. The
  reference if Campaign 4 outgrows a small-step trace semantics.
- **Iris** (Jung, Krebbers, Birkedal, Dreyer). Separation logic with
  adequacy as safety; the temporal-discharge inquiry's tool if it ever
  runs.
- **Proof by reflection and `vm_compute`** (Grégoire and Leroy, ICFP
  2002; `native_compute`, Boespflug, Dénès and Grégoire, CPP 2011).
  Campaign 5's mechanism.
- **Checked C formalization** (Li, Liu, Hicks et al.). A Coq model of
  bounds-checked C with a trap-or-correct theorem; the closest published
  relative of Campaign 3.
- **CHERI and Morello formal models** (Sail; the Isabelle proofs of
  Morello's capability monotonicity). Capability-as-identity semantics
  at the hardware level.
- **Verasco** (Jourdan et al.). A verified abstract interpreter for C:
  what Campaign 5 would become if the finder were trusted; the reason it
  is not.
- **FilPizlonator** (`FilPizlonator.cpp`, staging `af813053`).
  `scheduleChecks`, laundering inference, escape analysis: the analyses
  nanofil treats as sources, not oracles.
- **The Power of Prolog** (Triska). The style nanofil keeps on the
  Prolog side.
- **nanofil's own docs**: [campaign.md](campaign.md),
  [pizlonation.md](pizlonation.md), [lifetime.md](lifetime.md),
  [m7.md](m7.md), [forward.md](forward.md), [half.md](half.md),
  [bounds.md](bounds.md), [schedule.md](schedule.md). The side
  conditions in these are Campaign 3's lemma hypotheses.
