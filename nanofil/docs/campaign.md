# The campaign: executable capability semantics

This is the foundation and current direction of nanofil. Read it before
changing its semantics or factoring. [../PLAN.md](../PLAN.md) tracks
milestones; [factorings.md](factorings.md) records completed refactorings.
The historical frontend roadmap below is not the next work queue.

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
(a heap check's evidence for later scalar accesses in its block,
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
later scalar uses of a heap proof only within M7's block-local rule;
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
   block-local scalar reuse in [m7.md](m7.md)). Give an analysis explicit facts and
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
- **SWI for now.** Trealla is paused (October 2026): work and measure on
  SWI-Prolog, keep to the shared dialect, and come back to Trealla later.
- **Report honestly.** Say what a step made clearer and where the
  structure still differs from what it describes. Track line counts
  with `git diff --stat` as a symptom (a factoring that only adds lines
  should say what it bought), but do not optimize for them.
- **Coordinate.** Shared files (`c_lower.pl`, `filc_amd64.pl`, `ir.pl`,
  `interp.pl`) may have other owners; see AGENTS.md.

## Where we stand (October 2026)

Rounds 1 and 2 are logged in factorings.md. An outside review in
October 2026 found:

- **Succeeding:** each C typing rule now has one home in `c_types.pl`
  as a short case analysis citing its paragraph (`castable/2`,
  `assignable/3`, `arms_type/5`, `composite_type/3`,
  `binary_operands/6`, `unary_operand/3`, `expression_category/3`,
  `modifiable_lvalue/2`). Merging the copies closed about 15 gaps
  against clang, each with a test.
- **Not yet shorter:** round 1 was about −80 lines; round 2 was about
  +190 in `src/`.
- **Still two engines:** the judgment (`expression_type/3`) infers
  types but checks little; `c_lower.pl` raises 71 of the frontend's 78
  semantic errors, and asks the judgment about subtrees again (`&`,
  `?:`, null pointer constants, modifiable lvalues), which is quadratic
  on nested `?:`.

When this review was written, four walks traversed the same C
expression grammar, each with its own idea of types and categories
(steps 3 to 5 below made them one tree, read three ways):

| Walk | Where | Lines |
| --- | --- | --- |
| Lowering | `c_lower.pl`: `obj//3`, `rvalue//3`, `decay//3`, `convert//3` | ~380 |
| Judgment | `c_types.pl`: `expression_type/3`, `expression_category/3` | ~120 |
| Integer constants | `c_types.pl`: `const_eval/4`, `kind_binary`, `const_convert/4` | ~150 |
| Address constants | `c_lower.pl`: `addr_const/5`, `lvalue_const/5`, `expr_chunk/7` | ~130 |

Smaller ones: scalar-type facts spread over eight tables (`int_info/3`,
`rank/2`, `unsigned_of/2`, `type_class/2`, `load_op/3`, `store_width/2`,
`narrow_ext/2`, `conversion_int_type/2`); C operators tabled about six
times (`c_parse`, `c_types`, `c_lower`), with punctuators and
identifier characters defined in both `c_lex.pl` and `c_pp.pl`. (The
Fil-C checks, stated separately by `filc_amd64.pl` and `interp.pl`, now
have an IR form: [pizlonation.md](pizlonation.md).)

## Completed frontend design: one typed tree

Steps 3–5 below implemented this design. Its rationale is retained here:
elaborate each full expression once into a typed tree, and let every
consumer fold over it: IR emission, integer constants and address
constants. One description of what each C expression is, read three ways.

```prolog
% X     ::= val(Type, Node) | obj(Type, Place) | fun(Type, Designator)
% Place ::= local(Name) | global(Sym) | deref(X) | at(Place, Off)
%         | literal(Lit) | complit(Type, Init)
% Node  ::= int(N) | float(Bits) | conv(Conversion, X) | bin(Op, X, X) | ...
% Conversion ::= load | decay_array | decay_function | int(From, To)
%              | int_float | float_int | ptr_int | int_ptr | bool | void
%              | null_ptr
```

- The category is the principal functor, so consumers dispatch in
  clause heads. Conversions are explicit `conv/2` nodes named after
  C11 6.3; `binary_operands/6`'s converted operand types are exactly
  the conversions to insert.
- `elaborate/4` (E, Env, Loc, X) raises the C diagnostics, keeping the
  current message texts (`tests/reject.sh` matches on them) or changing
  reject tests deliberately.
- `expression_type/3` and `expression_category/3` become projections of
  the tree. `c_lower` loses `decay//3`, `convert//3`'s case analysis,
  `assign_convert//5`, `cond_type//4`, `modifiable//3`, `expr_type//3`
  and most `sema_error` calls; `obj//3` becomes `place//2` and
  `rvalue//3` becomes `value//2`. The estimate is −300 to −400 lines
  net.
- Incremental and byte-identical: introduce a `src(E)` bridge node for
  forms not yet elaborated, which lowering handles the old way; convert
  one form at a time; elaborate once per full expression, never per
  subexpression. Keep literal symbol numbering and the order of fresh
  temporaries as they are today. `#if` elaborates with `Env = pp`.
- Rejected alternative: computing constants by lowering and running
  `interp`. A constant context must refuse an oversized shift count or
  a zero divisor, where the IR masks the count and traps. (Signed
  overflow is a constraint violation by C11 6.6p4, but `const_eval`
  wraps it as clang's default folding does; see [ub.md](ub.md).)
  `interp` is a good test oracle, not the implementation.

## Frontend roadmap and implementation record

Update the status column when a step lands, with its commit.

| # | Step | Verify | Status |
| --- | --- | --- | --- |
| 1 | Commit the snapshot gate, `tests/snapshot.sh`. | Plant a one-token change in `arith_op/3`; the gate fails. | Done: 1006 outputs; the planted change made 6 differ. |
| 2 | One scalar table (`scalar/5` or similar) replacing the eight scalar-fact tables; one C operator table replacing `binop/3`, `assign_op/1`, `binary_kind/2`, `cmp_op/3`, `arith_op/3`, `compound_op/2`; one punctuator and identifier-character definition shared by `c_lex.pl` and `c_pp.pl`. | Snapshot identical; `pptest.sh`; unit tests and Nix checks on both hosts. Expect about −100 lines. | Done, −53 lines: `integer_type/4` and ir's `narrow_type/3`; `c_operator/4` with `compound_assignment/2`; c_lex's `punctuator/1`, `digraph/1` and character classes, shared by c_pp. Not done: `const_arith/4`, `cmp_op/3` and `arith_op/3`, which map C ops to IR ops and belong to step 3. |
| 3 | `elaborate/4` as the judgment: `expression_type/3` and `expression_category/3` become projections, and the elaborator raises diagnostics. | Assert old and new agree on every subexpression the snapshot reaches; snapshot identical; reject tests reject. | First part done: `elaborate/3` builds the tree, the two old predicates are its projections, and 15,413 queries agreed with the old judgment. Second part done: every operand is elaborated (call arguments, assignment sources, comma left operands, `?:` conditions, `sizeof` operands, `va_arg`'s list), and `src(E)` is gone. No child failed to elaborate on the snapshot or on zlib and Lua. Builtin arguments, statement-expression blocks and compound-literal initializers stay as source. Third part begun: c_lower judges each full expression with `elaborate/4` first, and `fault/4` diagnoses one that cannot be typed with lowering's messages, in its evaluation order. The elaborator now checks the constraints lowering did (modifiable targets, assignment and argument conversions, call arity, scalar conditions and logical operands, `&` of a value), and on the corpora raises 20 diagnoses itself with lowering's texts. It declines only where lowering refuses first something C allows (unsupported types, structs by value, `va_arg`, statement expressions). Remaining for step 4: delete lowering's duplicate checks as each form lowers from the tree. |
| 4 | Lower from the tree, form by form, through `src(E)`: literals and conversions (deleting `decay//3`, `assign_convert//5`), then places, then `?:` and assignment, then calls. Delete `obj//3` and `rvalue//3`. | Snapshot identical after every form. | Done. `rval//3` elaborates, then `lower//3` and `place//3` translate the tree; nothing lowers from source any more, and the source argument is gone. Deleted: `obj//3`, `rvalue//3`, `decay//3`, `expr_type//3`, `lower_call` and the duplicate checks for `?:`, assignment, `++`/`--`, casts and calls. Each node has one clause, with its C11 section: places (identifiers, `__func__`, string literals, compound literals, `*`, `.`) and values (constants, conversions, operators, `&&`/`||`, `?:`, assignment, calls, builtins, casts, `va_arg`, `sizeof`/`alignof`/`offsetof`, statement expressions, members of struct values). A cast, compound literal or `va_arg` keeps its type name in the tree, so lowering reads it again with the VM check. c_types now owns the remaining judgments: `assigned/4` for returns, initializers and builtin arguments, and `unsupported_type/3` for what nanofil refuses, which `fault/4` reports instead of declining (the long double literal's error now has its line). `assign_convert//5` remains as that judgment then `converted//3`, until returns and initializers become tree nodes. |
| 5 | Integer and address constants as folds over the tree: `const_eval/4` loses its own typing, `addr_const`/`lvalue_const` fold places to `sym(S, Off)`. | The `#if` cases against `clang -E`, `pptest.sh`, snapshot, `nanofil-zlib`, `nanofil-lua`. The four walks should be one. | Done. `const_eval/4` elaborates, then `folded/3` does arithmetic on the tree with the elaborator's conversions (`binary_operands/6` gives a comparison's common type); `kind_binary` lost its typing. `#if` elaborates with `Env = pp`: `env_int_type/3` at constants and int-yielding operators states 6.10.1p4 once, and refuses floating constants there. Null pointer constants are judged on the elaborated tree, not by elaborating the source again. c_lower's `address_constant/5` and `place_constant/5` replace `addr_const/5` and `lvalue_const/5`, one clause per tree node, which closed two gaps against clang, both now in `tests/c/static-array-address.c`: `&x[1][2]` (an array lvalue that decays) and `0 + 0` as a null pointer. Snapshot identical apart from cproc's `initializer-nested-array-address.c`, which now compiles. −16 lines in `src/`. |

## Fil-C lowering before target emission: basic foundation complete

Steps 3–5 established the frontend's boundary: c_types judges a C
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
an opt-in, independently checked scalar stack cache ([m6.md](m6.md)).
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
