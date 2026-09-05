# Development plan

## Purpose and current baseline

Test whether Prolog makes the semantics and safety conditions of an assembly
translator easier to express, review, and extend. Generated-code quality
matters, but a shorter implementation is useful only if its assumptions
remain visible. Trealla is the implementation host for this experiment.

The first spike is complete: DCG parsing, scalar value tracking, consecutive
read grouping, independent structural validation, and executable x86-64
output through Fil-C-generated C. The Nix check covers the table-entry
example, arithmetic, negative plans, runtime safety failures, and explicit
rejection of ARM64. See [README.md](README.md) for the precise subset.

Milestone 1 is also complete: instruction effects and the semantic contract
are explicit, grouping decisions are inspectable, and native differential
tests cover that executable subset. Milestone 2 is also complete: pointer
copies, `leaq`, integer stores and annotated pointer loads/stores. Milestone
3 is complete: typed basic blocks, flag values and conditional control flow.
Milestones 4–7 remain planned. Follow them in order; keep each extension small enough
to review with its semantic rules and tests. The parked zstd port is motivation and
potential future fixture material, not an active package migration or a
requirement to revive its builds now.

## Rules for extending the experiment

- Keep accepting and rejecting input explicit. Never pass an unknown
  instruction through to an assembler or silently ignore its effects.
- Specify value widths, pointer associations, memory effects, flags, and
  failure behavior before implementing a new instruction family.
- Preserve the unoptimized path as a differential reference. Keep each
  optimization independently selectable as more passes appear.
- Require successful, complete analysis before removing protection. An
  unknown result, resource limit, or analysis exception must retain checks
  or reject compilation; it must never become evidence of safety.
- Separate optimizer proposals from validation. A validator should check
  local, explicit obligations rather than rerun the optimizer's search.
- Keep experiments downstream of the pinned toolchain. Compare compiler
  output paths before accepting any change that would rebuild LLVM.
- Update supported-subset documentation and the Nix check in the same
  change as each extension. Commit and push completed, tested slices as
  experiments; leave unfinished or unrelated package work separate.

## 1. Make the semantic contract explicit

**Status: complete.** `effects.pl` owns the finite instruction catalogue and
normalized actions/effects; `ir.pl` consumes its typed reads and writes.
`accesses.pl` separates traced proposals from independent validation.
`--emit-effects` and `--explain` expose those decisions, and
[SEMANTICS.md](SEMANTICS.md) records the contract and runtime obligations.
This milestone retained the original instruction subset and classified
flag effects. Milestone 3 subsequently added flag values and consumers.

**Deliverable:** extract instruction effects from the original `step`
clauses in `ir.pl` into a shared relation consumed by lowering and available
for inspection. Keep the current executable subset unchanged initially.
Describe register reads/writes and widths, pointer versus integer values,
flag effects, memory accesses, and control flow. Include source locations
in errors and explain why a proposed read group was accepted or rejected.

Document which facts come from annotations, which follow from instruction
semantics, and which require runtime checks. In particular, distinguish a
read group from an already-established bounds check: today's validator
proves the former, while Fil-C still supplies the latter.

**Acceptance:** existing examples and tests retain their behavior. Table-
driven tests cover every supported instruction form and representative
illegal forms. Diagnostics identify the offending source line and missing
condition. Add malformed-source and generated small-program tests with
bounded execution, recording failures as small permanent fixtures.

**Evidence at completion:** all 29 instruction forms have table-driven coverage; 20
malformed-source fixtures check diagnostics. The native oracle executes
148 deterministic small programs and compares 37,888 exact results per
grouped/ungrouped variant. The original 32,000-case lookup checks and Fil-C
safety failures still pass. The table-entry example's grouped and ungrouped
C remain unchanged. Normalizing masked shift counts in the scalar example
also leaves its compiled assembly unchanged. This work reuses the existing
compiler/runtime.

**Review question:** can a reviewer find the complete meaning of an
instruction without reconstructing assumptions across several passes?

## 2. Add straight-line pointer operations and stores

**Status: complete.** Pointer-preserving register copies and `leaq`
with a pointer base, integer index and nonnegative displacement are complete.
The effect relation declares type preservation; lowering keeps fresh pointer
values pointer-typed through copies and derivation. Read planning treats
these operations as barriers. Integer stores now have explicit write
effects and unconditional grouping barriers. Tests cover aliased
inputs/destinations, overlapping stores, read-only destinations, capability
failures, boundary crossing and native return-value/full-buffer comparisons.
Pointer loads/stores use a same-line `#! ptr` annotation, have explicit
eight-byte alignment and pointer value-type effects, and lower to typed C
pointer accesses. They are never merged with integer reads.

**Evidence:** the table covers 36 instruction forms and 36 malformed-source
fixtures. Native execution compares 46,336 return/full-buffer outcomes
per variant. Fil-C callers check pointer round trips and self references;
15 failure modes per variant exercise slot/pointee bounds, lifetime,
alignment, write permission and real address bits without a capability.
Bytewise writes to a preexisting pointer slot are tested separately from
fresh integer-only storage. Negative displacements remain explicitly
outside the accepted contract, including for `leaq`.

**Deliverable:** support pointer-preserving register copies and a narrow
`lea` subset, followed by integer stores and explicitly annotated pointer
loads/stores. Represent pointer values and their associated capabilities
without routing them through integer temporaries. Keep branches and calls
unsupported for this milestone.

Track access width, read/write permission, and alignment separately. Add
stores as ordering barriers before considering any alias analysis. Do not
merge reads across a store merely because their address expressions differ.
Decide and document negative-displacement semantics without accidentally
introducing signed C overflow or losing x86 address behavior. Address
wraparound remains outside the contract until handled deliberately.

**Acceptance:** a small read/modify/write routine agrees with a C reference;
pointer-copy and pointer-round-trip tests preserve capabilities. Include
aliasing stores, read-only destinations, absent capabilities, boundary
crossings, unaligned integers, and pointer-alignment failures. Verify that
non-null integer bits cannot manufacture an accepted pointer.

**Review question:** which effects invalidate a previously known address
or memory fact, and where is that rule encoded?

## 3. Introduce basic blocks and conditional control flow

**Status: complete.** `cfg.pl` constructs explicit blocks, resolves targets,
filters unreachable blocks and joins typed register/flag states with a
finite topological worklist. Every reachable predecessor must supply a
usable value. Pointer parameters carry the incoming pointer's own capability.
`flags.pl` models condition dependencies and flag identities; C recipes
implement actual values. The edge validator is independent of edge
construction and checks transfers against recorded exit states. Edge
assignments use temporary values before overwriting destinations. Read
grouping remains inside a block; `--linear` retains the previous reference.
Reachable cycles are explicitly rejected until milestone 4.

**Evidence:** 61 instruction forms, 48 malformed-source fixtures, and
mutation tests for changed/missing/mistyped edge inputs, targets and
conditions. The original 181 native programs pass through four variants
(block/linear, grouped/ungrouped). Another 525 branch programs agree with
native x86 on 134,400 return/full-buffer outcomes per variant, including
all 16 conditions and flag joins. Fil-C callers check 4,096 pointer
selections, stores and swaps per variant, seven safety failures through
both arms, and an executable cyclic edge assignment. These include a
successful access on one predecessor followed by selection of a different
capability whose address bits denote the already-read object.

**Deliverable:** add explicit blocks and edges, then a bounded set of
comparisons and conditional branches. Model the flags those branches read;
do not infer a condition from the nearest textual comparison. Define joins
for scalar values and pointer associations, including conditional pointer
selection and swaps.

Initially keep optimizations inside a block. Use an explicit finite
worklist for dataflow and distinguish may-information from must-information:
reaching definitions can accumulate alternatives, while reusable protection
must hold along every incoming path. Specify what a join does when pointer
origins differ. Lower parallel edge assignments without clobbering values.

**Acceptance:** diamond-shaped control flow agrees with an independent
reference, including both arms and all comparison outcomes. Test a check
present on only one predecessor, differing pointer origins, stale flag
values, unreachable blocks, and cyclic swaps in edge assignments. Invalid
or unresolved joins must fail explicitly or retain a conservative lowering.

**Review question:** does the representation preserve the address and its
capability together for whichever value the program actually selects?

## 4. Complete one bounded decoder-shaped loop

**Deliverable:** extend the block representation to backedges and loop-
carried values, then implement a tiny table decoder: load a table entry,
write decoded bytes, advance input/output positions, and repeat with an
explicit bound. Start with one stream and integer operations already
covered by earlier milestones. Add bit operations only as the fixture
requires them; do not import zstd's full assembly as the first loop test.

Continue using Fil-C C lowering, allowing the compiler to handle roots,
safepoints and ABI details. Document the termination behavior of compiler
analyses independently from the runtime loop's termination.

**Acceptance:** randomized valid cases match a C oracle in bytes written,
returned values, and final positions. Exercise zero iterations, last-entry
and last-output boundaries, malformed inputs, backedge pointer changes,
and input/output aliasing under the stated contract. Both optimized and
unoptimized modes must retain runtime safety. Inspect generated assembly
for unexpected calls, repeated checks and spills before timing it.

**Review question:** is this a usable semantic model of a decoder loop,
rather than a collection of special cases for one input file?

## 5. Explore check reuse with explicit obligations

**Deliverable:** represent established protection separately from memory
operations and define its validity interval. Start with reuse of an earlier
successful covering check, where fault timing is easiest to preserve.
Treat wider or earlier checks as a separate transformation with an explicit
contract for traps and observable effects.

A proposal must name the capability/value identities, byte range,
permission, alignment, dominating check, and intervening effects. Validate
coverage and validity on every path, including overflow. Until calls,
frees, safepoints, concurrent mutation, and capability changes have defined
invalidation rules, treat them conservatively as barriers.

Keep the compiler-backed backend honest: a source-level proof does not by
itself remove Fil-C's machine checks. Inspect what C lowering can express
and what the existing compiler actually eliminates. Do not introduce an
unchecked escape mechanism just to make a benchmark improve.

**Acceptance:** mutation tests deliberately omit predecessors, alter
capabilities, shrink ranges, change permissions, and insert invalidating
effects; the validator must reject each broken proposal. Correct plans
must preserve outcomes and failure behavior under the chosen contract.
Measure emitted checks as well as source-level groups.

**Decision:** only introduce Trealla tabling if it helps this analysis and
has an explicit completeness/error outcome. Test cycles, exceptions,
resource limits, and partial answers against a worklist reference first.
The current tabling driver's caught worker exceptions are a known concern,
not evidence that a returned set is complete.

## 6. Decide whether a direct backend is justified

This is a decision milestone, not an automatic rewrite. First record what
is limiting the compiler-backed path: missing semantics, inability to
express a validated optimization, or generated-code quality. Direct
assembly emission expands the trusted implementation substantially.

If warranted, create a pinned ABI contract covering entrypoints, scalar
and pointer arguments/returns, capability layout, stack frames, GC roots,
safepoints, runtime calls, failure paths, and register preservation. Test
one leaf function first, then nested calls and GC-sensitive pointer
liveness. Retain the compiler-backed path as an oracle where both support
the same program. Add register allocation only with liveness/interference
validation and pressure-heavy fixtures.

**Acceptance:** independent Fil-C callers and callees interoperate; bad
accesses fail cleanly; live capabilities survive calls and collections.
Document which obligations the backend checker verifies and which remain
trusted. No claim of memory safety should rest solely on matching successful
outputs against upstream SaRCAsm.

For ARM64, first reuse the architecture-neutral IR and implement a small
matching leaf slice with real execution tests. Until that exists, retain
explicit rejection. Do not conflate different flag, addressing, alignment,
or calling-convention rules behind a shared instruction spelling.

## 7. Evaluate representative routines and choose the next scope

Only after the smaller slices pass should zstd-sized routines become a
candidate. Inventory the specific missing instruction forms and state
behavior before porting one. Other workloads are equally acceptable if
they provide a clearer test of the architecture.

For each candidate, compare the C reference, unoptimized translation,
optimized translation, and upstream SaRCAsm where compatible. Record exact
revisions, inputs, toolchain paths, code size, and build commands. Use
repeated interleaved timings, CPU affinity, and hardware counters where
available. Account for host contention and distinguish frontend compilation
time from generated-program runtime. Correctness and safety gates precede
performance conclusions.

**Acceptance:** publish a reproducible result, including regressions and
unsupported cases. Promote no variant to a default package merely because
it builds. Choose the next extension from demonstrated needs and evidence
about clarity, validation burden, and generated code.

## Immediate next change

Start milestone 3 with an explicit basic-block graph and validated edges.
Keep the current straight-line path as a reference. Define typed block
inputs and joins before implementing a diamond-shaped branch, and keep
read grouping inside individual blocks.

Add comparisons and a small conditional-branch family only alongside
their actual flag-value semantics. Track which instruction defines each
flag and reject undefined or unavailable flag reads. The first execution
fixture should select between integer values and then between pointers
from different origins; both paths must retain the selected capability.
Test malformed targets, incompatible or uninitialized incoming values,
stale flags and parallel edge assignments before introducing loops.
