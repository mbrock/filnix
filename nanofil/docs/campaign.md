# The campaign: executable capability semantics

This is the foundation and current direction of nanofil. Read it before
changing its semantics or factoring. [../PLAN.md](../PLAN.md) tracks
milestones; [archive/factorings.md](archive/factorings.md) records completed
refactorings, and [archive/frontend.md](archive/frontend.md) the frontend's
one typed tree, which is done and not the next work queue.

## The ambition

nanofil is both a working C compiler and an executable account of
Fil-C's capability semantics. Compiling programs and investigating their
meaning are two uses of the same explicit IR and relations. The purpose
is not to reproduce LLVM's optimizer in Prolog. It is to make the memory
model, safety obligations, and reasons for accepting a transformation
readable, executable, and eventually amenable to small formal proofs.

The organizing distinction is **requirement, evidence, implementation**.
An access requires authority over an object's bytes. A runtime check is
one way to establish it; static reasoning, still-valid earlier evidence,
or a combination may establish it too. An optimizer must justify a
cheaper implementation of the requirement, not silently weaken it.
Today nanofil accepts immediate checks and one reviewed reuse rule
(a heap check's evidence for later scalar accesses on every path forward,
[m7.md](m7.md)), not arbitrary certificates. Extending the accepted
evidence further is future semantic work.

nanofil should read like the standards it implements. A clause of
`c_types.pl` should be recognizable as a paragraph of C11, a clause of
`ir.pl` as a sentence about the IR, a clause of `filc_amd64.pl` as a
fact about the Fil-C ABI. Each fact is stated once, as a relation, and
its consumers read that relation. This reduces drift; it does not prove
the shared rule correct. Independent observations, native comparisons,
and explicit proof obligations remain necessary. Some relations can run
backwards, finding inputs or generating the programs they describe.

The aim is adequacy of structure, not brevity: the shape of the code
should be the shape of what it describes, the way a proposition pictures
its fact. A rule of C belongs in one clause group named for it, a
distinction C draws (lvalue or not, constant or not, which conversion)
belongs in a principal functor, and a step C takes implicitly (an
lvalue conversion, a promotion) should be visible as a term. Clarity is
not concision: supporting more of real C will keep making nanofil
larger, and that growth is fine when each new fact has its obvious
place. Condensing and unifying are the means; line counts are a symptom
worth watching, not the goal.

The model is Markus Triska's [The Power of Prolog](https://www.metalevel.at/prolog):
clean representations with cases told apart by their principal functor,
case analysis in clause heads, one description read in several
directions, and relations that describe what holds rather than
procedures that compute it. AGENTS.md's "Purity where it pays" records
where we deliberately stop short (`#=` and `if_/3` on ground compiler
data).

## The memory model comes before the optimization

C syntax identifies operations but does not uniquely determine their
safe interpretation. Fil-C supplies a capability model where ordinary C
permits undefined behavior. nanofil must state which part of that model
it implements, rather than assume that source programs are already safe.

- **Address is not authority.** A pointer has address bits and a
  capability identifying an object. Computing another live object's
  address does not acquire its capability. Bounds, rights, and lifetime
  are properties of the identified object, not just an address range.
- **Identity is shared.** Freeing through one alias invalidates the
  others. A stored capability is an identity, not a snapshot of bounds.
  The [lifetime oracle](lifetime.md) states the current explicit-free
  semantics and its limits.
- **Effects matter to evidence.** Calls, polls, allocation and
  pointer-memory helpers have distinct effects. A fact about alignment
  need not expire when a not-freed fact expires. Rooting and the runtime's
  treatment of concurrent free are separate from detecting explicit free.
- **Representation protocols need semantics too.** Printing a pointer
  and parsing its address back does not preserve its capability. The
  Ghostscript [adaptation](../../patches/ghostscript-filc.patch) retains
  pointers in an exact pointer table. This supplies a runtime mechanism,
  not an assertion that arbitrary parsed addresses are safe. A future C
  annotation could describe such a protocol or propose an invariant; it
  must not manufacture authority or act as an unchecked safety axiom.

Checked IR makes these distinctions executable: `flight` states address
and capability sources, `check` and `check_local` produce class `a`, and
`check_function` produces class `f`. Raw operations cite their evidence.
The validator requires each check's immediate first use, and accepts
later scalar uses of a heap proof only within M7's forward rule;
the interpreter can expose an invalid raw access as `unchecked(Why)`.
The [pizlonation contract](pizlonation.md) owns these rules, including the
closed pointer-memory effect protocols and the indivisible `p` pair.

## FilPizlonator is a source of analyses, not a proof oracle

The pinned LLVM pass already combines static reasoning and runtime
enforcement. It is one module pass containing several analyses and
lowerings, not one undifferentiated check-insertion algorithm. These
observations are from staging
[`af813053ecb5`](https://github.com/mbrock/fil-c/commit/af813053ecb5a5ff27292bfede8d3a9e870d4c8e);
the [ABI findings](abi-findings.md) explain how to obtain its small source
snapshot. Method names below are in `FilPizlonator.cpp`.

| Analysis | Facts and purpose |
| --- | --- |
| `inferPointerAsIntLaunderingForFunction` | `Bottom`, `Definite(P)`, `Top` track a capability source through integer dataflow; phis/selects can select matching capabilities. Recovering a source does not prove the resulting address in bounds. |
| `scheduleChecks` | Separate validity, alignment, bounds, writability, not-free and auxiliary-metadata requirements. Forward propagation removes established checks; backward propagation schedules requirements earlier; a final forward pass removes new redundancy. |
| `findNonescapingAllocasInFunction` | Backward lifetime facts (`Undetermined`, `Live`, `Zombie`) and escape analysis choose general managed storage or local representations. This contains the comment “Vive l'interprétation abstraite!” |
| `lazifyAllocasInFunction`, `computeFrameIndexMap` | Initialization and liveness analyses delay allocations and reuse GC-root storage; derived pointers can share a root when its identity and dominance justify it. |

The check scheduler reasons about canonical pointers and constant offsets,
not arbitrary symbolic arithmetic. Its forward joins retain common facts;
its backward joins are more restrictive. It can retain spatial facts
across a poll while requiring renewed temporal validation. A poll is not
therefore a blanket prohibition on loop-invariant spatial-check motion.

These are trusted C++ analyses that directly produce code, not independent
proof certificates. Their assertions and final LLVM `verifyModule` check
representation invariants, not semantic preservation. Ordinary scalar
optimization largely belongs to the surrounding LLVM pipelines.

## Safety and behavior preservation are separate obligations

Three different claims must not be conflated:

1. **Checked-IR safety:** under stated initial-state and environment
   assumptions, every admitted execution of a validated checked module
   avoids `unchecked`. This is a theorem to establish about validation
   and semantics, not a theorem obtained merely by running the validator.
   [formal.md](formal.md) calls it soundness of checking. It allows
   traps: a valid program with a memory error still panics (a Fil-C
   check fails), and that a particular program never panics is a
   separate, per-program theorem built on this one (formal.md's
   Campaign 7).
2. **Transformation correctness:** a pass produces admissible output and
   preserves or refines the original program's observations. Replacing
   every program with a trap could satisfy the first claim and fail this
   one. Object correspondence matters when allocations move or disappear.
3. **Implementation correctness:** native lowering and the runtime realize
   those semantics, including roots, helper exits and call channels. An IR
   proof alone does not establish this claim.

Observations need a precise definition. The current `opt:refines/2`
compares outcomes, with specific treatment of undefined behavior,
constrained results and allocation-relative pointer results. It is not
a general relation on memory states, effect traces or object bijections.
Pizlonation tests compare returns and traps; unknown external effects,
asynchronous free and general symbolic memory are outside the interpreter.
Do not infer a stronger theorem from that test interface.

In particular, upstream check scheduling can move failure before an
ordinary or volatile store: it does not promise every preceding effect
on an execution containing an invalid access. That is not permission to
weaken nanofil's current acceptance criteria. Before adopting such motion,
state the permitted failure timing, diagnostics and observable effects,
and extend the oracle and review the contract. First reuse experiments
should preserve the existing behavior, without speculative earlier traps.

## Evidence has a scope and a trust boundary

- **Structural validation** checks this module against the IR's rules.
  Accepted class-`a`/`f` uses carry a small, conditional safety argument;
  they are not Agda proof terms or a proof of the whole compiler.
- **Concrete differential tests** compare executions. **Bounded symbolic
  queries** can find counterexamples, or establish their absence within
  completely searched finite domains. Unknown inputs are supported only
  where the interpreter is relational: addresses, allocation sizes,
  capabilities and floats must be concrete when used. Exhausted fuel,
  unsupported execution or incomplete search is inconclusive.
- **Translation validation** checks a particular transformation against a
  contract. M6's scalar-cache checker already does this for its selected
  instruction stream; it does not verify instruction selection, the
  original emitter, or the runtime.
- **Universal proofs** would establish explicitly quantified claims over
  a specified model. Prolog success and executable `doc/3` examples do not
  supply those proofs. Shared source rules can share a bug as well as a
  definition; independent validation must not repeat the producer's choice.

AI-assisted proof discovery is a possible producer of evidence, not a new
authority. Agents could spend substantial offline effort finding an
invariant, auxiliary lemmas, or a replacement for one hot path. A routine
build should replay a deterministic check of the resulting evidence, not
ask a model whether it is convincing. The theorem, allowed assumptions,
program, dependencies, semantics and checker version must be identified;
freezing dependencies does not freeze external inputs. No added postulate
or unchecked annotation may silently discharge the safety obligation.
Timeout or failure leaves the checked reference implementation available.

This is an architectural direction, not an implemented certificate
format or a decision to port the compiler to Agda, Twelf or another proof
assistant. Formalizing one small rule and its correspondence to the
executable model would be useful; proving a disconnected model would not
certify emitted assembly.

## The next work extends evidence, not an optimizer framework

1. **State a small obligation and its effects.** For an initial scalar
   check-reuse experiment, identify the pointer, covered bytes, rights,
   alignment and lifetime facts, their invalidators, and the observations
   that must remain unchanged. Start inside the current oracle's domain.
2. **Extend acceptance before relying on new evidence.** Design the IR,
   validator, interpreter and emitter contract together (done for
   forward scalar reuse in [m7.md](m7.md)). Give an analysis explicit facts and
   merge/transfer rules, and a checker an independently stated acceptance
   rule. Keep runtime checks for obligations not established. Review the
   safety change before implementation.
3. **Make the counterexamples discriminating.** Aliasing free, wrong
   allocation identity, branch-specific knowledge, misalignment, rights,
   helper effects and changed trap behavior should defeat incorrect
   proposals. Use finite complete searches where possible, native/GC tests
   where the interpreter abstracts effects, and one narrow formalization
   if it clarifies the contract. Passing these tests is not a universal
   soundness proof.
4. **Expose the actual computation.** Keep passes independently callable
   and show their real intermediate IR in the playground. As evidence
   becomes explicit, show why an obligation is discharged or remains a
   runtime check. That explanatory view must read the compiler's result,
   not reconstruct a second analysis in the UI.

The existing `promote`, `copy` and `local_storage` selections establish
the modularity pattern: ordinary Prolog relations, explicit products,
fixed legal ordering, and no required microscopic-pass framework. A
substantial analysis may remain one coherent module. Broad arithmetic
optimization and general register allocation are not prerequisites for
this semantic work, nor is an end-to-end compiler proof.

## How we work

- **Behaviour-preserving by default.** A refactoring keeps the IR
  byte-identical on the snapshot: `tests/snapshot.sh` compares the
  working tree with a revision over every test and corpus input.
- **Every behaviour change has a fail-first test.** When merging two
  copies of a rule changes what nanofil accepts or computes, compare
  with clang, add a test that fails before the change and passes after,
  and say so in the commit.
- **SWI by default.** Keep to the shared dialect. The small backend parity
  check runs on Trealla too; full frontend/interpreter work there remains
  paused ([archive/hosts.md](archive/hosts.md)).
- **Report honestly.** Say what a step made clearer and where the
  structure still differs from what it describes. Track line counts
  with `git diff --stat` as a symptom (a factoring that only adds lines
  should say what it bought), but do not optimize for them.
- **Coordinate.** Shared files (`c_lower.pl`, `filc_amd64.pl`, `ir.pl`,
  `interp.pl`) may have other owners; see AGENTS.md.

## Fil-C lowering before target emission: basic foundation complete

Steps 3–5 of the frontend record ([archive/frontend.md](archive/frontend.md))
established the frontend's boundary: c_types judges a C
expression once; c_lower emits from that judgment. Pizlonation now uses
the same boundary: checked IR states what Fil-C requires, and the target
implements those terms rather than rediscovering the requirements from
a high-level pointer operation.

The checked stage keeps `p` pairs but makes their construction and
ordinary memory effects explicit. A subsequent `filc_abi` product
describes frames, calls, getters and origins before native placement.
Fusing a proof with its immediate use remains a target instruction-
selection choice, with a separate liveness view at the same index.
Neither lowering introduces independently scheduled lower temporaries.

| Step | Contract and gate | Status |
| --- | --- | --- |
| Explicit function-target checks | `check_function` produces an ephemeral `f`; `raw_call` consumes it immediately. Target validity is distinct from signature dispatch and callee traps. Same assembly, including buffered returns, roots and setjmp layouts. | Implemented; see [pizlonation.md](pizlonation.md). Memory checks and poll edges were already explicit. |
| Flight-pointer and runtime effects | Define address/lower propagation and aux/barrier operations once, with a semantics and validator. State which operations may exit to the runtime; preserve ensure-aux's rooted reload. Review before adoption. | Implemented: `flight` and the closed pointer-memory effect lists are validated and executed, preserving one interval, roots and layout. Checked inputs bypass the unchecked-only optimizer. Snapshot: 1014 identical outputs; native boxed-load/replacement and actual ensure-aux exit coverage. Proof adjacency is unchanged. |
| ABI lowering | Describe frame-root placement, prologues/exits, call signatures and fast/generic dispatch, getters and origins before AMD64 instruction selection. Keep setjmp's returns-twice storage distinct. Snapshot each extracted responsibility; exercise clang interop in both directions and forced GC. | Implemented in [fe019c0](https://github.com/mbrock/filnix/commit/fe019c0cb8cb4c5e2afb2f2d63ec2006cfa79620): `filc_abi` produces consumed plans, not just constants. Snapshot: 1014 identical outputs; native interop, setjmp, variadic and exception-channel coverage. Global data serialization and physical placement remain target-side; C++ unwinding remains unsupported. |
| Lifetime semantics and M5 storage | Give free/invalidation an interpreter meaning before check optimizations; then review exact-sized non-escaping stack objects and their rooting/lifetime rules. | Lifetime implemented in [3251c43](https://github.com/mbrock/filnix/commit/3251c438043f37e40246bd6ca585fd34b679beaf); conservative LocalExplicit storage in [c3d740d](https://github.com/mbrock/filnix/commit/c3d740d4ca80d40167aba411d69a74b93f96dce3). Exact-bounds-only selection preserves refinement; special stack-aux roots preserve pointer contents across GC. No native stack address becomes a heap lower. General C local-OOB precision remains deferred; see [m5.md](m5.md). |

This closes the basic foundation for the documented subset. The four
Nix gates cover the combined pipeline; native root-removal and effect
mutations fail, not just malformed-term tests. M6's first slice is now
an opt-in, independently checked scalar stack cache ([archive/m6.md](archive/m6.md)),
since retired.
General register allocation, M7 check removal, broader local selection and
general symbolic memory validation remain later work. Pointer pairs are
still indivisible, and global data serialization and physical layout remain
target-side. The next optimization must extend these contracts rather than weaken
refinement or hide a new safety decision inside emission.

The review followups close two earlier correctness gaps: native range
checks detect unsigned subtraction borrow and reject unencodable sizes;
unsupported float loads escape before promotion, including in dead code.
Durable native probes now cover actual ensure-aux exits with last-use
operands, lower-only donors across collection, and both exception-return
channels restoring the parent frame. These are regression guarantees for
the bounded foundation, not a general memory-safety certification.

Do not add a parallel hierarchy of wrappers just to make a pass appear
in a diagram. A new term earns its place when it states a fact the
validator, interpreter and emitter can all read. A new module earns its
place when it owns a coherent specification. This may add code while
making the boundary explicit; the measure is whether there are fewer
independent accounts of the same rule.

## Further semantic investigations

These are research directions, not additional acceptance claims:

- **Source rules and their coverage.** The C11 citations can index
  typing rules and report which clauses the corpora exercise. Relate
  frontend lowering to the IR's chosen semantics; do not identify C's
  undefined behavior with permission to violate capability safety.
- **One arithmetic, three readings, cross-checked backwards.** With the
  typing relations table-driven, the elaborator can generate
  well-typed constant expressions over a finite type universe; then
  compare `const_eval`, `interp(lower(E))` and clang where their domains
  agree. Constant-expression rejection and IR wrapping are deliberately
  different outside that overlap. First round done ([arith.md](arith.md)):
  a generator over c_types' typing relations, the overlap stated as
  classes, a slice in the Nix check and `tests/arith.sh` for larger
  searches. It found unchecked shift counts, folded `INT_MIN / -1` and a
  lowering crash on casts of undefined constants. Signed overflow in
  `+ - * <<` still wraps in `const_eval`, as clang's default folding
  does; it is now a measured class rather than an assumption.
  [ub.md](ub.md) states Fil-C's policy on undefined behaviour (its
  KillUB pass, what each kind of UB does at `-O0` and `-O2`) and where
  nanofil's IR agrees.
- **Relations between interpretations.** Investigate unchecked versus
  checked execution, heap versus local storage, and concrete versus
  abstract execution. State the object correspondence and environmental
  assumptions each comparison needs. These provide small candidates for
  formalization without claiming a verified C frontend or native backend.
- **A formal campaign.** [formal.md](formal.md) plans the step beyond
  them: the core of ir.pl and interp.pl transcribed into Rocq, the
  runtime's promises as one page of axioms, a machine-checked theorem
  that a valid checked module never reaches `unchecked`, and checks
  removed only where an extracted checker replays a certificate.
