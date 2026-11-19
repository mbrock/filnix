# The formal campaign: checked IR, certificates, and Rocq

November 2026. This extends [campaign.md](campaign.md), which states
nanofil's foundation; read that first. The campaign below is a plan,
and each campaign ends with a note in `docs/` that says what it found;
the table below says what is built.

The [live GNU Hello campaign](hello-glibc.md) proves compiled glibc
bodies. It trusts contracts for calls into the runtime at the
[zsys boundary](zsys.md). The former proof against per-function libc
contracts and the standalone proof examples are no longer in the build.

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
| 1 | The core model in Rocq, agreeing with the interpreter | Gallina syntax, semantics, `valid` | under way: syntax, memory and small-step semantics in `nanofil/rocq/`, agreeing with `interp:run/5` on every core-subset run line, and `valid` for functions, data and aliases, agreeing with `ir:valid_module/1` on every core-subset mutant of the corpus and of tests/gen.pl's Fil-C modules, both under every `--checks` mode with and without `-O`, and of the tests/c/prog programs with aliases and weak, thread-local or constructor data; floats (`Ieee.v`) and variadics are in the subset, so every corpus run line is compared and all of Lua 5.4.7's functions decode into it; `setjmp` is in the subset too, so ldo.c's `luaD_rawrunprotected` is judged by `valid`, while its second return is not modelled and a run stops at the setjmp, with Lua's state-free functions run by the gate ([rocq.md](rocq.md)); tests/gen.pl's Fil-C modules now reach `renew_if`, `limit` with `check_limit`, and `renew_hull`, with frees and traps; found and fixed: a renew of a freed variadic snapshot was `unchecked(span)`, now a trap as native renew gives; dominance now transcribes cfg.pl's `cfg_idoms/2` and `dom_intervals/3`, so the validator judges Lua's lvm.c; the model's runtime is Campaign 2's module type; the three data findings are decided (data items have the header's shapes, a call of data traps, names are unique) |
| 2 | The runtime as one page of axioms, each probed natively | `docs/runtime-axioms.md` | first version: [runtime-axioms.md](runtime-axioms.md) and `Module Type Runtime` in `nanofil/rocq/theories/core/Runtime.v`, eleven axioms read against staging `18b6663`, each with a native test in tests/c/prog/axiom-*.c (the eighth, `address_space`, from Campaign 3's coverage lemma; the ninth and tenth, `free_keeps_ids` and `free_checked`, from Campaign 3's theorem; the eleventh, `free_succeeds`, from Campaign 7's program logic, test axiom-free-succeeds.c); the interpreter's instance proves them all, and three readiness obligations without a native test (the third, `freed_bounds`, from Campaign 3's half check); Campaign 3's machine runs over any instance; since 2026-11 the safepoint axiom is the collector's alone, `collector_live` (no region changes at a safepoint; test axiom-collector-live.c), with `safepoint_lifetime` and `rooting` lemmas from it, because a handler or thread that frees is the program's code |
| 3 | Soundness of checking: the validator's theorem | `valid_no_unchecked`, no admits | started: [Machine.v](../rocq/theories/soundness/Machine.v) runs the steps over any `Runtime` and proves `ready` an invariant of every run, and every step a `step_rel` step or a safepoint action; [Coverage.v](../rocq/theories/soundness/Coverage.v) proves the coverage lemma, given `objects_fit` (its proof needs only objects ending at or below 2^64; the axiom says 2^48, native's bound, which `hull_covered` needs: mbrock's decision); the interpreter broke that (`rocq/tests/huge-object.ir`, a valid module run unchecked), and now traps where native Fil-C refuses an allocation, with the runtime axiom `address_space` supplying the hypothesis in every state of a run that starts ready; a valid module's initial data has no size limit, so the theorem takes "the run starts ready" as a hypothesis (mbrock's decision; starting the heap above the data is the planned fix); [Evidence.v](../rocq/theories/soundness/Evidence.v) proves the evidence pass sound instruction by instruction and across an edge; [Persistence.v](../rocq/theories/soundness/Persistence.v) carries it over whole runs: in every state of a run, a frame that is not doomed runs no raw access or raw call to `unchecked` except by `hull_covered`, using that the runtime changes no region at a safepoint the pass keeps facts across (`spares`; the pass keeps facts across three such; once a hypothesis, now a lemma for every runtime, `spares_any` from `collector_live`); [Dominance.v](../rocq/theories/soundness/Dominance.v) proves the validator's dominator intervals sound for every function (a run enters only blocks with an interval, and dominance holds across each edge), which the reuse forms' single-definition chains rest on; [Interval.v](../rocq/theories/soundness/Interval.v) proves the offset intervals `offset_interval/8` answers sound, wherever the names they walk hold their definitions; [Sites.v](../rocq/theories/soundness/Sites.v) proves that a single definition's operands are not defined again where it dominates; [Identity.v](../rocq/theories/soundness/Identity.v) proves that no run loses an object, since the runtime's free keeps identities (the axiom `free_keeps_ids`, first a hypothesis), so a check that passed passes again or traps; [Single.v](../rocq/theories/soundness/Single.v) proves that in every frame of every run each single definition whose site dominates the point replays, its operands unchanged and its memory persisting; [Chain.v](../rocq/theories/soundness/Chain.v) reads guard chains and pointer distances off it and proves the first reuse form: along every run, an access `hull_covered` accepts gives no `unchecked` (`interp_access_checked`, closed), with the evidence invariant now carrying that the live facts' pointers dominate the point (Dominance.v's `dom_meet`, from the nearest-common-ancestor property of `cfg_idoms/2`); [Renew.v](../rocq/theories/soundness/Renew.v) proves the next three: along every run, no renew, renew over a hull or half check the pass accepts gives `unchecked` (`interp_reuse_checked`, closed), with `address_space` now saying objects start at or above 0 and a readiness obligation that freed objects are empty (`freed_bounds`); [Guard.v](../rocq/theories/soundness/Guard.v) proves `renew_if` and `check_limit` the same way (`interp_guard_checked`, closed), with no new hypothesis; planning `check_ahead`'s doomed frame found a valid module the interpreter ran to `unchecked(ahead)`, a check whose start wrapped onto the need's end modulo 2^64, now refused (`near_offset/1` of K + Lo in `ahead_insts/8` and the pass, [rocq.md](rocq.md), "A need past 2^64"); [Ahead.v](../rocq/theories/soundness/Ahead.v) reads the pass's needs back as facts at each point and proves its one sweep computes them; [Doomed.v](../rocq/theories/soundness/Doomed.v) proves that along every run a frame a `check_ahead` doomed never steps to `unchecked` (`interp_doomed_checked`, closed), carrying the validator's need as facts at the frame's point; [Soundness.v](../rocq/theories/soundness/Soundness.v) assembles `valid_no_unchecked`: along every run of a checked module that starts ready, no step is `unchecked` (`interp_valid_no_unchecked`, closed, a plain instance), with no runtime hypothesis beyond the ready start (`spares` was one while the safepoint stood for signal handlers too, mbrock's decision; since 2026-11-09 every runtime meets it by `spares_any` and the statements drop it; a handler a program installs could still free a checked object at a pointer store's aux exit, a constraint on verifying handlers), the axioms `free_keeps_ids` and `free_checked` (each with a native test), and external calls other than `free` stuck until Campaign 4's contracts |
| 4 | Observations, refinement, and external calls | a trace semantics; `opt:refines/2` as trace inclusion | [ExternalCalls.v](../rocq/theories/external/ExternalCalls.v) defines the contract and effect relations. [ExternalMachine.v](../rocq/theories/external/ExternalMachine.v) adds direct-call transitions and proves that labelled runs preserve readiness, identities, and Campaign 3's invariants. Native trace coverage and refinement remain open. |
| 5 | Static discharge by certificate | `discharged(Cert)`, `discharge_ok`, a Prolog finder | not started |
| 6 | Integration with Filnix and the playground | the `nanofil-check` gate | not started |
| 7 | Trap-freedom of a pinned Nix closure | `never_panics` for one linked program | The [GNU Hello proof](hello-glibc.md) verifies the linked image over the audited runtime boundary. |

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
Ieee.v, variadic functions (`va_args`, `va_arg`), `touch`, `raw_cas`
(2026-11-11), and
`setjmp`: its validation is ir.pl's (a zero SaveMask but for
`sigsetjmp`, no locals, and no reuse form in its function), but the
second return is not modelled, so its step is stuck as the
interpreter's is and no theorem follows a `longjmp`. Deferred: vectors,
the unchecked `cas` and the other atomics, `asm_fixed`, plain mode.

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
definition to its page in [the model](../rocq/theories/core/Values.v), drawn
by dterm-rocq:

| Rocq definition | Source | Notes | In the model |
| --- | --- | --- | --- |
| `cap := CNone \| Obj base \| Ro base \| Fn f \| External n` | `cap_access_res/7`: `none`, `obj(Base)`, `ro(Base)`, `fn(F)`, `ext(N)` | identity, never bounds | [cap](../rocq/theories/core/Values.v#cap) |
| `ptr := { ptr_addr : Z; ptr_cap : cap }` | `ptr(Addr, Cap)` | the indivisible flight pair | [ptr](../rocq/theories/core/Values.v#ptr) |
| `region := { r_base; r_end; r_kind; r_life }` | `region(Base, End, Kind, Life)` | bounds live here, looked up by identity | [region](../rocq/theories/core/Memory.v#region) |
| `mem := { m_bytes; m_regions; m_aux }` | `mem(Bytes, Regions, Next, Aux)` | aux maps slot address to stored capability; Next became the freshness condition `fresh` | [mem](../rocq/theories/core/Memory.v#mem), [fresh](../rocq/theories/core/Memory.v#fresh) |
| IEEE arithmetic on bit patterns | ieee.pl | exact rationals, one rounding function; x87's NaN rule for `x` | [round_ratio](../rocq/theories/core/Ieee.v#round_ratio), [ieee_binary](../rocq/theories/core/Ieee.v#ieee_binary) |
| `cap_access_res`, `access_res` | `cap_access_res/7` | the trap reasons in the backend's order | [cap_access_res](../rocq/theories/core/Memory.v#cap_access_res), [access_res](../rocq/theories/core/Memory.v#access_res) |
| syntax: func, block, inst, value, module | ir.pl's header tables | core subset only; one constructor per IR functor | [inst](../rocq/theories/core/Syntax.v#inst), [func](../rocq/theories/core/Syntax.v#func), [module](../rocq/theories/core/Syntax.v#module) |
| small-step `step : genv -> config -> step_result`, and `step_rel` | `interp:run/5` | fuel-indexed; `step_rel` takes any fresh base where `step` asks for one | [config](../rocq/theories/core/Semantics.v#config), [step](../rocq/theories/core/Semantics.v#step), [step_rel](../rocq/theories/core/Semantics.v#step_rel) |
| `valid : module -> option bool` | `ir:valid_module/1` | computable, reflection-ready; mirrors the coverage and evidence rules, data and aliases; `None` when a function is outside the subset | [valid](../rocq/theories/core/Validate.v#valid), [valid_func](../rocq/theories/core/Validate.v#valid_func), [valid_data](../rocq/theories/core/Validate.v#valid_data), [valid_alias](../rocq/theories/core/Validate.v#valid_alias) |

The [outcomes](../rocq/theories/core/Semantics.v#outcome) are the
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
  [Coverage.v](../rocq/theories/soundness/Coverage.v), given `objects_fit`, every
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
  [Evidence.v](../rocq/theories/soundness/Evidence.v), and over runs in
  [Persistence.v](../rocq/theories/soundness/Persistence.v); where the runtime
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

The shared contract framework describes calls that leave the compiled
module. The live glibc proof uses it for calls into the runtime. The
extracted driver still models only `free` when it encounters an external
call.

The remaining refinement goal is to restate `opt:refines/2` as trace
inclusion, connect the Prolog and extracted models to external-call
observations, and compare those observations with native runs.

### Campaign 4, milestone 1: a standalone contract boundary

[ExternalCalls.v](../rocq/theories/external/ExternalCalls.v) is independent of
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
  before `heap_req` rounds the extent.

In the live campaign, [OsWrite.v](../rocq/glibc/zsys/OsWrite.v) and
[OsWritev.v](../rocq/glibc/zsys/OsWritev.v) use `StreamBytes` to record
what a write accepts at the runtime boundary. The event does not record
bytes still buffered in glibc or certify final delivery to a reader.

### Campaign 4, milestone 2: guarded machine integration

[ExternalMachine.v](../rocq/theories/external/ExternalMachine.v) is a labelled
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

Completed calls take one labelled step. The independent
`ExternalCalls.prefix` relation describes allowed intermediate effects,
not every intermediate machine state of a native execution. The
`mstep_refines` theorem covers only the core machine.

### GNU Hello and the runtime boundary

The earlier program examples and per-function libc contracts are
described in the [previous version of this page](https://github.com/mbrock/filnix/blob/eee53aaacf071c842045fd14e8e91dd4187dd6ab/nanofil/docs/formal.md#campaign-4-observations-refinement-and-the-environment).
The current proof instead links Hello with compiled glibc and uses the
[OS registry](../rocq/glibc/zsys/OsRegistry.v) for calls into the runtime.

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

[The Hello census](trap-census.md) measures the checked IR of GNU Hello.
The live proof uses a linked image of Hello and userland glibc, with
Hello's function bodies taken directly from the generated image objects
through [HelloBodies.v](../rocq/glibc/hello/HelloBodies.v).
[HelloImageFnLink.v](../rocq/glibc/hello/HelloImageFnLink.v) checks that
symbol lookup in that image reaches the bodies named in the proof.
[HelloStartNeverPanics.v](../rocq/glibc/hello/HelloStartNeverPanics.v)
states the resulting safety claim and its remaining premises.

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
- **External-call preconditions.** Each call out of the linked image
  must meet the corresponding runtime contract.
- **Allocation sites** are not obligations: refusing is the runtime's
  choice.

The census is mechanical and needs no proof. It classifies Hello's
checks by shape and shows which need a per-function triple and which
Campaign 5 can discharge.

### The quest, in steps

The [obligation census](trap-census.md) counted the checks before the
proof began. The [linked Hello proof](hello-glibc.md) starts from the
compiled closure, rather than assuming contracts for uncompiled libc
functions. The next targets in this plan are `ls` and, as a stretch,
OpenSSH’s server.

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
