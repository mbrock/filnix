# nanofil

nanofil is a C compiler written in Prolog that emits Fil-C's memory-safe
ABI, and an executable account of what that safety consists of: every
check is a term in its IR, an interpreter gives the IR a meaning, and a
Rocq model proves that a validated module's checks are enough. Every
page about it is listed here.

## Start

- [A guide to nanofil](guide.md): one C function through every stage,
  the ideas to hold, a map of the modules and where to start a change.
- [Compile C in the browser](../web/play/): nanofil on SWI-Prolog in
  WebAssembly, drawing the syntax, IR and assembly it makes.

## Explainers

- [How Fil-C works](filc.md): capabilities, the collector, safepoints
  and the libc sandwich, the memory-safe C nanofil targets.
- [How Iris works](iris.md): from Hoare logic to Iris, how it is built
  in Rocq, and nanofil's machine as an Iris language.
- [Concepts](concepts/): each term the Prolog, the Rocq and these
  documents share, explained once.

## The formal campaign

- [The formal campaign](formal.md): checks removed only where a
  machine-checked proof says they cannot fire; the plan, campaign by
  campaign, and what is built.
- [The model, read as Rocq](../rocq/): the Rocq development drawn as
  structure, with its proofs' states.
- [A program logic for never_panics](logic.md): moving the proofs that
  programs never panic to Iris, and how far it has come.
- [Campaign 0: Lua's residual checks](residual.md): which checks remain
  after nanofil's own evidence, measured on Lua.
- [Campaign 1: the core model in Rocq](rocq.md): the model, the
  validator and the machine, the decisions taken and the gates.
- [Campaign 2: the runtime as axioms](runtime-axioms.md): the facts
  about Fil-C's runtime the model takes as given, each with a native test.
- [The Gallina backend](gallina-backend.md): the plan for a nanofil IR
  compiler written in Gallina and extracted, first to OCaml, then to
  C++ and a Fil-C library.
- [Campaign 7: trap-obligation census](trap-census.md) and
  [native libc contracts](libc-contracts.md): what a whole program
  (Hello) needs proved, and the libc boundary it relies on.

## The compiler

- [The source, read as Prolog](../src/): every module drawn as terms.
- [The campaign: executable capability semantics](campaign.md): the
  foundation and its priorities; read it before semantic work.
- [Pizlonation](pizlonation.md): the checked stage's contract, its
  proofs, safepoints and pointer effects.
- [The explicit-free lifetime oracle](lifetime.md): the interpreter's
  model of `free`.
- [Fil-C ABI findings](abi-findings.md): the ABI as verified against the
  pinned Fil-C.
- [Undefined behaviour](ub.md): what Fil-C and nanofil do with
  overflow, shifts, aliasing and uninitialized reads.
- [Nonlocal returns](setjmp.md), [floating point](float.md),
  [fixed-register inline asm](asm-fixed.md) and
  [full-width vector access](vector-access.md): their contracts.
- [NFB, a bytecode for nanofil IR](nfb.md): an RFC draft for the IR as
  little-endian words, with one encoding per module; the numbers the
  encoder and decoder of [nfb.pl](../src/nfb.pl) assign.
- [dterm](dterm.md): how these pages draw Prolog and Rocq, and
  documentation as a relation; its [workbench](../web/workbench/)
  sets the same terms side by side.

### Check evidence

- [M7: reusing access-check evidence](m7.md): one check's proof covering
  later accesses, round by round, with the reviews.
- [Forward facts](forward.md) and [half checks](half.md): the `-O`
  default's evidence, as filcc's forward pass keeps it.
- [Scheduled checks](schedule.md): earlier traps as filcc's scheduler
  makes them; an opt-in prototype.
- [One branch for both bounds](bounds.md): the two bounds tests as one
  comparison.
- [Lowers per root](lowers.md): the GC-root contract of a frame.

## Measurement

- [Package survey](survey.md): how much of filnix's ported C builds with
  nanofil alone, and what stops the rest.
- [Code quality](perf.md): where `-O` spends its instructions, the
  benchmark gate and the plan.
- [Real C corpus](corpus.md) and [Lua 5.4](lua.md): whole programs
  built by nanofil, against filcc.
- [Upstream Fil-C's test suite](filc-tests.md): Fil-C's own tests built
  by nanofil, failures by kind.
- [One arithmetic, three readings](arith.md): constant folding against
  the interpreter and clang.

## Milestones

The milestones that are still partly reference; search M4 for a C
feature.

- [PLAN.md](../PLAN.md): milestones and decisions.
- [M3: pointer class and Fil-C lowering](m3.md),
  [M4: C frontend](m4.md) and
  [M5: analyses and promotion](m5.md).

## Archive

Records of finished or retired work, kept as written. What still holds
has moved into the code and the documents above.

- [Where it stands, October 2026](../../pages/nanofil-status/): what it
  built, how fast its code ran and compiled, then.
- [The frontend's one typed tree](archive/frontend.md): the review,
  design and step-by-step record that made the frontend's four walks one.
- [Toward a shorter, truer nanofil](archive/factorings.md): completed
  refactorings and what each bought.
- [M1: IR, relational interpreter, QBE subset](archive/m1.md),
  [M2: naive x86-64 backend](archive/m2.md) and
  [M6: scalar stack caching](archive/m6.md), retired.
- [Prolog hosts](archive/hosts.md): Trealla and Scryer, measured in
  October 2026.
- [The handoff](archive/handoff.md): the original design notes.
