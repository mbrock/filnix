# nanofil plan

nanofil is a C compiler written in Prolog. Its IR and backend follow QBE,
and its output is x86-64 assembly in the Fil-C ABI. That assembly links
with clang-built Fil-C code and keeps Fil-C's memory-safety guarantees.
It is meant to be a small, readable reference implementation of what the
Fil-C pass does, not a replacement for it.

Background and design rationale are in [docs/handoff.md](docs/handoff.md),
kept as written. What was checked against the toolchain filnix actually
ships is in [docs/abi-findings.md](docs/abi-findings.md). Where the two
disagree, the findings win.

```diagram
 C source
    │  M4: DCG preprocessor + parser, cproc-style lowering, SysV struct
    ▼      classification
 ┌──────────────────────────────┐   M1: relational interpreter (CLP(Z))
 │ IR terms: ins/4, jumps, phis │◀── checks every pass; differential
 └──────────────┬───────────────┘    tests against real qbe
                │  M5: tabled analyses, SSA, promote, copy, alias
                ▼
 ┌──────────────────────────────┐
 │ IR with pointer class p      │
 └──────────────┬───────────────┘
                │  M3: pizlonate: flight pointers, checks, frame,
                ▼      pollchecks, getters, function objects
 ┌──────────────────────────────┐
 │ IR with explicit (ptr,lower) │
 └──────────────┬───────────────┘
                │  M2/M6: isel, regalloc, DCG emission
                ▼
 GNU as  ──▶  link with filcc  ──▶  runs under the Fil-C runtime
```

## Decisions

These were open in the handoff. Each has a default chosen so work can
start. Reversing one is cheap until the milestone it names.

1. **Pointer class: a new IR class `p` (decided by M3).** Fil-C needs to
   know pointerness at every load, store, call, phi and frame slot. An
   annotation on `l` would have to survive every pass, while a class is
   carried by construction and is visible to clause indexing. QBE's passes
   mostly treat class as opaque, so the middle-end cost is in `ext`/`trunc`
   rules and the casts `ptrtoint`/`inttoptr`, which become explicit ops.
   Phase one (M1–M2) uses plain QBE classes only.
2. **Target: the filnix pin, Fil-C 0.686 (`163fae5`), x86-64 only.**
   Origin layouts differ from upstream head (see the findings), so the
   static data layouts live in one table. `nanofil/probes/run.sh` must
   pass before and after any pin change.
3. **Host: Trealla at a recent pinned revision.** nixpkgs has Trealla
   2.99.1, which predates native tabling. filnix already builds a recent
   Trealla under Fil-C (`pkgsFilc.trealla`, September 2026, with tabling
   fixes). Add a native build of the same revision for development speed,
   and keep the Fil-C build as the "memory-safe compiler" demo host. Keep
   code Scryer-compatible where it is free to do so.
4. **Reference QBE: nixpkgs `qbe` 1.2 to start.** The phase-one subset
   (integer ops, memory, branches, calls) is stable across versions. Pin a
   newer revision only if a test needs it.
5. **Assembler: GNU `as`, linking through filcc.** M0 showed this works,
   and it keeps clang out of nanofil's own pipeline.
6. **Unsupported features are rejected, never passed through.** At first
   these are `setjmp`/`longjmp`, inline asm, defining variadic functions,
   pointer atomics, bitfields, VLAs, `_Complex` and threads. Unknown input
   is a compile error with a source location.
7. **Relationship to [experiments/sarcasm-prolog](../experiments/sarcasm-prolog/README.md).**
   It is related but separate. That experiment translates assembly to C and
   lets clang apply Fil-C. nanofil emits the Fil-C ABI itself. nanofil
   adopts its rules for extending (see below) and its habit of documenting
   the supported subset alongside each Nix check, but shares no code.

## Rules for extending

- Every pass is checked by the M1 interpreter on its tests: same inputs
  before and after the pass, same observable results.
- Safety checks may be removed only on a complete, successful analysis.
  An unknown result, a resource limit or an exception keeps the check or
  rejects compilation. It never counts as evidence of safety.
- Keep the unoptimized path selectable and use it as the differential
  reference for each optimization.
- Purity wherever it pays (handoff, "Lessons from The Power of Prolog").
  Impurity is confined to the driver: versioned facts at pass boundaries,
  I/O, and time budgets. Each impure spot gets a comment saying why.
- Changes to what is considered safe (check elimination, rooting, getter
  skipping) get an Oracle review first, as for the compiler itself
  (root AGENTS.md).

## Milestones

### M0. Ground truth on the pinned toolchain

**Status: complete.** The ABI probes, the pin comparison and the answers
to the handoff's empirical questions are in
[docs/abi-findings.md](docs/abi-findings.md). A hand-written assembly
function links with clang-built Fil-C code. Direct calls, indirect calls
through our getter and function object, and a rejected wrong-signature
generic call all behave as expected. `nanofil/probes/run.sh` reproduces
this.

### M1. IR terms, relational interpreter, QBE subset parser

**Deliverable:** clean IR terms (handoff "Proposed design" item 1) and a
CLP(Z) interpreter for `w`/`l` integer ops, `alloc`, loads and stores over
a byte-addressed memory, `jmp`/`jnz`/`ret`, phis and calls between IR
functions. It also needs a DCG parser and printer for the matching QBE
text subset; start from the handoff's `parse.pl` design. The scratch files
did not survive, so rewrite it.

**Acceptance:**

- Round-trip parse and print on a fixture set.
- On every fixture, the interpreter's results match `qbe` output assembled,
  linked with a C harness and run natively.
- One demonstration of running backwards, such as "find inputs where
  these two functions differ", to show that the interpreter is pure.

**Also decides:** how memory is modelled, as an assoc or an explicit store
term. This is the hardest part to keep relational.

### M2. Naive backend, plain SysV

**Deliverable:** IR to x86-64 assembly with every temp in a stack slot, a
fixed scratch-register isel DCG and plain SysV calls. Backpatched labels
are unbound variables, as in Thinking in States.

**Acceptance:** every M1 fixture compiled by nanofil gives the same result
as the interpreter and as `qbe`. This isolates emission bugs from Fil-C
lowering bugs.

### M3. Pizlonation and Fil-C ABI emission

**Deliverable:**

- The `p` class and explicit `ptrtoint`/`inttoptr`. `inttoptr` yields
  lower 0, with no laundering analysis.
- A pizlonate pass, IR to IR, producing flight pointers. Every access gets
  the full check sequence. Pointer loads and stores go through outline
  helpers, with no inline fast path yet.
- Frame push and pop, with a lower slot per pointer value and a naive
  "every pointer temp gets its own slot" policy. Entry stack checks and
  back-edge pollchecks.
- The fast convention with R9 and stack splitting and `has_exception`;
  calls to clang functions through their `FI<sig>` symbols plus weak
  thunks of our own.
- Function objects, getters and generic entries. Functions only at first;
  globals with pointer initializers come in M7.

**Acceptance:**

- IR programs that use pointers run under Fil-C.
- Calls work in both directions with clang-built objects, including
  pointer arguments past R9 and wrong-signature calls.
- Every safety failure class traps with a sensible origin: out of bounds
  below and above, null capability, write to readonly, use after `free`,
  and a call through a non-function.
- A GC stress test shows that rooting holds: allocation churn, with
  collections forced through `zgc_request_fresh` and `zgc_wait`, and
  scribbling and verify modes where the runtime offers them.

### M4. C frontend subset

**Deliverable:** a preprocessor and parser in DCGs, plus cproc-style
lowering with C types known, emitting `p` for pointers. SysV struct
classification as recorded in the findings. Covers integers, pointers,
arrays, structs and unions without bitfields, all statements, string
literals, function pointers and calls to libc.

**Acceptance:** a growing corpus of small C programs gives the same output
under nanofil and under `filcc`. Candidate sources are cproc's tests
(ISC, `.c` paired with expected `.qbe`, also usable against M1), the
c-testsuite, and programs from filnix's ports. Each unsupported feature
gets a rejection test.

### M5. Middle end and translation validation

**Deliverable:** tabled CFG, dominator, liveness, alias and loop
relations, plus SSA construction, `promote`, copy elimination and
`ALoc`/`AEsc` escape classification. Non-escaping locals stay on the
stack; escaping ones move to the heap, as Fil-C does.

**Acceptance:** each pass validated by the interpreter on the corpus, and
a symbolic before/after equivalence query on small functions. A measured
answer to the handoff's open question on versioned facts versus incremental
tabling, at realistic sizes (hundreds of blocks, small live sets).

### M6. Instruction selection and register allocation

**Deliverable:** cut-free isel that enumerates tilings, then selects the
minimum-cost one. Register allocation in CLP(Z) with a search budget and a
greedy fallback in the style of QBE's spill-then-assign.

**Acceptance:** same corpus results with lower instruction counts, and
allocation time bounded on every corpus function. The budget and fallback
answer the handoff's open question about predictability.

### M7. Check optimization and the rest of the ABI

**Deliverable:**

- Inline pointer load and store fast paths.
- Check merging per canonical pointer, using M5 alias base-plus-offset
  facts. Redundant-pollcheck removal.
- Globals with getters, caches and relocation tables.
- Getter-free pointer-free readonly literals. This is the findings' claim,
  and it needs Oracle review and the M3 GC stress test before it ships.

**Acceptance:** fewer checks in the output than M3, the same trap behavior
on the M3 failure suite, and Oracle sign-off on each removal rule.

### M8. Demo

Compile something recognizable, such as a small ported program, with
nanofil running on Fil-C-built Trealla. Package it as
`nix build .#nanofil` with `checks.x86_64-linux.nanofil`.

## Still open

- How to model memory relationally without losing performance (M1).
- Versioned facts versus incremental tabling (M5), and the CLP(Z)
  allocation budget (M6). Both are measurement questions.
- In-process execution (`tcc -run` style) needs a native host that boots
  the Fil-C runtime. It is out of scope until after M8.
- Supporting `setjmp`, variadic definitions, atomics and inline asm, all
  rejected until a milestone claims them.
