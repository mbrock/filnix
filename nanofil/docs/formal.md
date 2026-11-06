# The formal campaign: checked IR, certificates, and Rocq

November 2026. This extends [campaign.md](campaign.md), which states
nanofil's foundation; read that first. The campaign below is a plan:
nothing in it is built yet, and each campaign ends with a note in
`docs/` that says what it found.

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

Three things fall out of a well-stated model beyond nanofil: a
definition of Fil-C independent of LLVM, which does not exist today; a
trusted base small enough to hand to the runtime's author as one page of
axioms; and, at the horizon, translation validation of filcc's own
output through the same checker, which is how the work would reach every
package in Filnix rather than only what nanofil compiles.

## The campaigns at a glance

| Campaign | Goal | Deliverable | State |
| --- | --- | --- | --- |
| 0 | Measure which checks survive `-O --checks=combined` | `docs/residual.md` | not started |
| 1 | The core model in Rocq, agreeing with the interpreter | Gallina syntax, semantics, `valid` | not started |
| 2 | The runtime as one page of axioms, each probed natively | `docs/runtime-axioms.md` | not started |
| 3 | The soundness theorem for the validator | `valid_no_unchecked`, no admits | not started |
| 4 | Observations, refinement, and libc contracts | a trace semantics; `opt:refines/2` as trace inclusion | not started |
| 5 | Static discharge by certificate | `discharged(Cert)`, `discharge_ok`, a Prolog finder | not started |
| 6 | Integration with Filnix and the playground | the `nanofil-check` gate | not started |

## Three claims, kept apart

[campaign.md](campaign.md) already separates three claims; the formal
work keeps that separation and attacks them in this order.

| Claim | Statement | Status today | This campaign |
| --- | --- | --- | --- |
| Checked-IR safety | Every execution of a validated checked module, under the runtime axioms and environment contracts, avoids `unchecked(Reason)` | `ir:valid_module/1` in Prolog, differential tests, bounded symbolic search | The central theorem, machine-checked (Campaign 3) |
| Transformation correctness | A pass's output refines its input's observations | `opt:refines/2`, ad hoc; `check_reuse:reuse_refines/2` and its kin per check pass | A trace semantics and refinement relation (Campaign 4); certificates for static discharge (Campaign 5) |
| Implementation correctness | Native lowering and the runtime realize the IR semantics | `amd64_regs_check.pl`, native difftests, snapshot gates | Out of scope for proof; strengthened by a native trace oracle only |

In scope: filc mode, the checked stage, the integer and pointer classes,
`check`, the `raw_*` accesses, `flight`, `poll`, `call` and `free`, and
the reuse vocabulary: `renew`,
`renew_hull(Lo, Hi, Rights, Align)`,
`half_check(Bound, Lo, Hi, Rights, Align)`, `span_test(Lo, Hi)` with
`renew_if(Lo, Hi, Rights, Align)`, `limit` with
`check_limit(Lo, Hi, Rights, Align)`, and
`check_ahead(Lo, Hi, Rights, Align, AHi)`. Deferred: floats
([ieee.pl](../src/ieee.pl) is a separate integer-only model and can
come later), x87, vectors, `cas` and atomics, `setjmp` (already excluded
from every reuse rule), `va_arg`, `asm_fixed`, plain mode.

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
it, and a one-line decision. Effort: days, not weeks; agents can do all
of it.

## Campaign 1: the core model in Rocq

Goal: a Rocq development that transcribes [ir.pl](../src/ir.pl) and
[interp.pl](../src/interp.pl) for the core subset, executes by
extraction, and agrees with the Prolog interpreter on the Lua test
suite.

The model is a transcription, not a design: the interpreter already made
the choices. What goes over, and from where:

| Rocq definition | Source | Notes |
| --- | --- | --- |
| `cap := None \| Obj base \| Ro base \| Fn f \| Ext name` | `cap_access_res/7`: `none`, `obj(Base)`, `ro(Base)`, `fn(F)`, `ext(N)` | identity, never bounds |
| `ptr := { addr : Z; cap : cap }` | `ptr(Addr, Cap)` | the indivisible flight pair |
| `region := { base; end_; kind; life }` | `region(Base, End, Kind, Life)` | bounds live here, looked up by identity |
| `mem := { bytes; regions; aux }` | `mem(Bytes, Regions, Next, Aux)` | aux maps slot address to stored capability; Next becomes an existential freshness condition |
| `access_res` | `cap_access_res/7` | the trap reasons in the backend's order |
| syntax: func, block, phi, let, store, flight, check, `raw_*`, jumps, poll | ir.pl's header tables | core subset only; one constructor per IR functor |
| small-step `step : config -> config + outcome` | `interp:run/5` | fuel-indexed; one outcome per interpreter outcome |
| `valid : module -> bool` | `ir:valid_module/1` | computable, reflection-ready; mirrors the coverage and evidence rules |

The outcomes are the interpreter's: `Ret v`, `Trap r`, `UB r`,
`Unchecked r` and `OutOfFuel` for `ret(V)`, `trap(Reason)`, `ub(Reason)`,
`unchecked(Reason)` and `out_of_fuel`.

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

Gates: the extracted interpreter and `interp:run/5` agree on every test
input and every corpus function (same outcome, same return value, same
trap reason); `valid` and `ir:valid_module/1` agree on every module in
the snapshot corpus, with and without `-O` and under every `--checks`
mode. Disagreement is a finding, not a failure, and gets a fixture.

Effort: the syntax and semantics are a few hundred lines of Gallina; the
validator transcription is the larger part because ir.pl's evidence
rules are intricate. Agents can transcribe; a person should review the
two or three places where the Prolog relies on cut order or ground-term
assumptions that have no Gallina counterpart.

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
under the Campaign 2 axioms, for the core subset and every reuse rule in
scope.

This is the theorem [campaign.md](campaign.md) names as "checked-IR
safety". It is about the validator, not about any program, and it is
where all the content lives: pizlonation soundness is then the trivial
fact that `pizlonate:pizlonate_module/2` emits valid modules.

Proof plan, in the order the dependencies run:

- **Coverage lemma.** A `raw_load` or `raw_store` whose address operand
  is a check that passed, with Lo ≤ Off, Off + Size ≤ Hi, alignment and
  rights as the validator requires, does not produce `unchecked(Reason)`.
  Pure arithmetic over `cap_access_res/7`.
- **Proof persistence.** Between a check and a raw use with only
  `evidence_preserving/1` instructions and unpolled edges on every path,
  no free occurred, so the capability still permits the same range.
  Needs the safepoint and lifetime axioms and an induction over the
  paths the validator inspects.
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
validator transcription (and `valid` rejects it). Effort: this is the
campaign that takes months, and the one where agents do well on the
arithmetic lemmas and badly on choosing the invariant; a person states
the invariant for proof persistence before agents are turned loose.

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
  contract: the capability authority it requires on its arguments (or it
  traps), the memory it may write, the objects it may allocate or free.
  `read(Fd, Buf, N)` requires write on [Buf, Buf + N), writes at most N
  bytes there, frees nothing. `malloc` mints a fresh region. `memcpy`
  needs read on one range and write on another. `free` is what the
  interpreter already does.

The contract table is the trusted base for everything about libc, so it
is built as a relation in Prolog first (replacing today's instantiation
error on `ext(Name)` accesses, and letting the oracle run programs that
call out), tested natively on the Lua suite's actual calls, and only
then transcribed as axioms in Rocq. Starting set: whatever the Lua test
suite links against.

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
footprint were too small. Effort: the trace semantics is a week of
design that should not be rushed; the contract table grows one function
at a time and agents can drive it from the corpus.

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
was cheap, say so. Effort: the checker and its soundness proof are a
month of focused work once Campaign 3's lemmas exist; the finder is a
Prolog afternoon per invariant shape.

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

## Inquiries and investigations

Questions the campaigns will force, or that could redirect them. None is
scheduled; each has a cheap first step.

| Inquiry | Question | First step | Could change |
| --- | --- | --- | --- |
| Integer-to-pointer | What capability does `itop` yield, and when does laundering recover one? nanofil ([launder.pl](../src/launder.pl)) and filcc (`inferPointerAsIntLaundering`) each encode an answer; the model must state one | Write the rule as a Gallina definition and diff the two implementations on the corpus | Which programs trap; Campaign 1's value model |
| Pointer `cas` | It compares addresses only and ignores capabilities, so an ABA on capabilities passes; why is that sound? | State the argument in one lemma (the access check still runs on the loaded pair) | Whether atomics enter the core subset |
| Intrinsic typing | Make `a` and `f` dependent types indexed by pointer, range and an epoch bumped at every safepoint, so coverage and persistence are typing, not a theorem | Prototype in Agda or Rocq on the `sum` example; compare proof effort with Campaign 3's extrinsic route | Campaign 3's whole shape |
| Temporal discharge | Proving no free between a check and a later access for heap objects needs ownership; is Iris worth instantiating for the IR? | Count how many Campaign 0 residual checks are flag-only after `renew`; if few, skip | Whether the Iris instantiation ever happens |
| Capability erasure | A pointer whose every use is proven could live as a raw address inside a region; interfaces stay fat | Define erasure for a single function with no stores of the pointer; measure on the benchmark | A second performance tier beyond check removal |
| Concurrency model | The single-thread model tolerates other threads' frees via retention; is a nondeterministic free-at-safepoint event enough to state the theorem for multithreaded programs? | Add the event to the semantics and re-check Campaign 3 | Campaign 2's axioms; Campaign 4's traces |
| libc inside the model | Compile musl (or Fil-C's libc) with nanofil, moving libc from axioms into the theorem | Survey which libc functions the corpus needs and whether nanofil's C subset covers them ([survey.md](survey.md)) | Campaign 4's trusted base |
| filcc translation validation | Map FilPizlonator's LLVM output into checked IR and run it through the same checker | Hand-translate one function's filcc output; list the vocabulary gaps | Reach: every package in Filnix, not only nanofil's |
| Floats | [ieee.pl](../src/ieee.pl) is an integer-only SSE2 model; transcribe it and prove it against a reference? | Differential-test the extracted version against the Prolog one | Whether `s` and `d` join the core subset |
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
- **People state invariants; agents prove lemmas.** Agents are strong at
  arithmetic lemmas, transcription, test generation and certificate
  finders, and weak at choosing the inductive invariant for Campaign 3's
  persistence lemma. State that invariant by hand before fanning out.
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
