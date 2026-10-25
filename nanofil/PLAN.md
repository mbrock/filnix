# nanofil plan

nanofil is a C compiler written in Prolog. Its IR started as a QBE
subset and is now its own (`src/ir.pl`, with `src/interp.pl` as its
meaning and `src/ir_text.pl` as its text), and its output is x86-64 assembly in the Fil-C ABI. That assembly links
with clang-built Fil-C code and keeps Fil-C's memory-safety guarantees.
It is meant to be a small, readable reference implementation of what the
Fil-C pass does, not a replacement for it.

Background and design rationale are in [docs/handoff.md](docs/handoff.md),
kept as written. What was checked against the toolchain filnix actually
ships is in [docs/abi-findings.md](docs/abi-findings.md). Where the two
disagree, the findings win.

```diagram
 C source
    │  M4: preprocess, parse, elaborate once, lower
    ▼
 ┌─────────────────────────────────┐
 │ Unchecked IR: p, memory, calls  │◀── M1 interpreter
 └───────────────┬─────────────────┘    validates before/after outcomes
                 │ M5: promote, copy, conservative local storage
                 │ M3: pizlonate
                 ▼
 ┌─────────────────────────────────┐
 │ Checked IR: flight, proofs,     │◀── same interpreter
 │ pointer effects, poll edges     │
 └───────────────┬─────────────────┘
                 │ filc_abi
                 ▼
 ┌─────────────────────────────────┐
 │ ABI plans: roots, entry/exit,    │◀── native interop and GC tests
 │ call channels, getters, origins │
 └───────────────┬─────────────────┘
                 │ AMD64 placement, instruction selection, emission
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
   Phase one (M1–M2) used plain QBE classes only.
2. **Target: filnix staging, Fil-C 0.687 (`35faf87`), x86-64 only.**
   No 0.686 compatibility. Static data uses staging's 48-byte origins and
   per-site setjmp lowers (see the findings). `nanofil/probes/run.sh` must
   pass before and after any pin change.
3. **Host: SWI-Prolog by default, Trealla also supported.** nanofil
   started on Trealla (a native build of the pinned revision, plus
   `pkgsFilc.trealla` as the "memory-safe compiler" demo host). From M5
   on, SWI-Prolog (nixpkgs, 9.2.9) is the default: it ran the tests 5 to
   25 times faster in a fraction of the memory, and it has a profiler.
   The code stays in Trealla's dialect; `src/swi/` adapts SWI to it, and
   `bin/nanofil` picks the host (`NANOFIL_HOST=swi|trealla`). The check
   runs everything on SWI and a short part on Trealla. Keep code
   Scryer-compatible where it is free to do so.
4. **Reference QBE: nixpkgs `qbe` 1.2 to start (retired).** The
   phase-one subset was checked against real qbe until October 2026,
   when the IR became nanofil's own and the qbe difftest was removed;
   the interpreter and native runs are the references now.
5. **Assembler: GNU `as`, linking through filcc.** M0 showed this works,
   and it keeps clang out of nanofil's own pipeline.
6. **Unsupported features are rejected, never passed through.** At first
   these are inline asm,
   pointer atomics, bitfields, VLAs, `_Complex` and threads. Unknown input
   is a compile error with a source location. Bitfields are now
   supported, laid out as SysV says and accessed through their storage
   unit (docs/m4.md).
   Direct setjmp-family calls and ordinary longjmp calls are now supported
   in Fil-C mode; see [docs/setjmp.md](docs/setjmp.md).
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

## The basic foundation is complete for the documented subset

Pizlonation states checks, flight construction and ordinary pointer-memory
effects in executable IR. Fil-C ABI lowering describes frames and calls
before AMD64 emission. Exact-sized nonescaping objects have explicit local
storage and collector metadata, with a conservative heap fallback.
Pointer pairs stay indivisible; this is not an IR of independently
scheduled address and lower temporaries.

The frontend refactoring is through campaign step 5: one elaborated
tree supplies lowering, integer constants and address constants. The
same separation on the Fil-C side now has these boundaries:

1. **State safety obligations in checked IR.** Memory checks and polls
   are done; function-target checks now also have a proof class and raw
   call, validated and interpreted. No checks are removed.
2. **Expose flight-pointer operations and their effects.** Pure pointer
   construction now uses `flight`: an explicit address calculation and
   lower source, validated and interpreted independently. The pair stays
   indivisible. Ordinary pointer accesses carry ordered aux, barrier,
   reload and payload effects, executed by interpreter and emitter.
   Phis, loads, calls and allocation still carry whole `p`s.
3. **Separate Fil-C ABI lowering from AMD64 emission.** Frame roots,
   entry/exit, fast/generic calls, getters and origins are products of
   `filc_abi`; physical stack/register placement and instruction spelling
   belong to the target. Setjmp snapshots and variadic cursors are
   explicit exceptions to ordinary value lifetimes. Global data
   serialization and relocations remain target-side.
4. **Complete the lifetime oracle before optimizing checks.** The
   interpreter now models free/invalidation, including aliases and
   stored capabilities. Named locals have fresh invocation identities,
   exact bounds and scoped lifetime cleanup. Their native stack-aux
   roots are distinct from ordinary heap lowers. Selection requires
   fixed-offset in-bounds accesses and a 4 KiB payload/aux budget; all
   unsupported candidates retain heap semantics.

Each boundary has a reviewed contract, interpreter evidence where the
effect is modelled, native interoperation and GC stress. Representation-
only changes preserve assembly; local-storage selection is checked by
before/after semantics and native rooting tests. M6 now has an opt-in,
validated scalar stack cache; general register allocation and M7 check
removal remain later work, as do general C local-OOB
precision, broader stack-local selection, general symbolic memory
validation and C++ unwinding. This is a stable foundation to extend,
not a claim to implement every Fil-C operation or all of C.
The detailed next steps are in [docs/campaign.md](docs/campaign.md).

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

**Status: complete.** See [docs/m1.md](docs/m1.md). The differential
tests found three qbe miscompiles and a Trealla use-after-free. The QBE
text parser and printer were later replaced by nanofil's own IR text
(`src/ir_text.pl`). Memory is
an assoc of concrete byte addresses, and symbolic addresses are deferred.

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

**Status: complete.** See [docs/m2.md](docs/m2.md). nanofil's own
assembly matches the interpreter on the fixtures, the random corpus and
the three qbe-bug repros that qbe gets wrong.

**Deliverable:** IR to x86-64 assembly with every temp in a stack slot, a
fixed scratch-register isel DCG and plain SysV calls. Backpatched labels
are unbound variables, as in Thinking in States.

**Acceptance:** every M1 fixture compiled by nanofil gives the same result
as the interpreter and as `qbe`. This isolates emission bugs from Fil-C
lowering bugs.

### M3. Pizlonation and Fil-C ABI emission

**Status: basic lowering and runtime acceptance complete.** See
[docs/m3.md](docs/m3.md) and [docs/pizlonation.md](docs/pizlonation.md). nanofil's Fil-C
output matches the interpreter's returns and traps, interoperates with
clang-built code in both directions, and survives a GC stress test that
catches planted rooting bugs. Checks, polls, flight construction and
pointer-memory effects are explicit IR; frame and call policies are ABI
products before emission. Pointer pairs remain indivisible.

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

**Status: done.** M4a through M4f are done, see
[docs/m4.md](docs/m4.md) and [docs/corpus.md](docs/corpus.md).
Broken into steps below. Probes at the pin
(compile `printf`, `puts`, globals and string literals with `filcc -S`)
settled the ABI questions first:

- A variadic call is an ordinary call with the call-site signature, for
  example `printf("%d %s\n", x, s)` calls `FI131273` = `(ptr, i64, ptr)
  -> int`. Variadic definitions now use generic-only entries and rooted
  argument snapshots; see the findings' variadic section.
- Clang calls every external function through a hidden weak thunk named
  `pizlonatedFI<sig>_f`. The thunk calls the getter `pizlonated_f`, checks
  that the result is a function object (special type, `ptr` equal to its
  aux pointer), then calls the fast entry if the signature matches and the
  generic entry otherwise, checking the returned size. libc is a shared
  library, so this is the only way to reach it.
- A global `g` is `pizlonatedDO_g` (header `{DO+16+size, flags << 48}` and
  payload), a 16-byte cache `GP_g`, a getter that returns the cached
  pointer or calls a slow path, and the slow path
  `filc_global_initialization_start` / `filc_execute_constant_relocations`
  / `filc_global_initialization_end`. Pointer-holding globals also have an
  aux array `DA_g` and a relocation table. A string literal is the same
  with flags GLOBAL | READONLY and no aux array.

**Decisions** (defaults, cheap to reverse during M4):

1. **Integers only.** No floating point in M4, as the deliverable says.
   Float types parse in declarations, because the headers use them, and
   any use of a float value is rejected.
2. **Real glibc headers** from filcc's sysroot, not private headers. The
   parser accepts the GNU subset they use: `__attribute__` (ignored),
   `__extension__`, `__restrict`, `__inline`, `__builtin_va_list`
   and asm labels (symbol renames, which must be honoured). The DCG
   preprocessor (M4e) reads these headers directly; `filcc` supplies only
   the target's predefined macros, feature answers and include paths.
3. **Globals and string literals move into M4** from M7, in the same naive
   form clang emits: getter, cache, registration, relocations. M7 keeps
   the getter-skipping optimization that needs Oracle review.
4. **External calls go through clang-style thunks**, replacing M3's
   "signature mismatch is a link error".
5. **Locals all live in `alloc`**, as cproc's output does before
   `promote`; the Fil-C lowering heap-allocates them. M5 promotes them.
6. **Struct copies** are word-wise `load(p)`/`store(p, ...)` over
   8-aligned words and narrower integer copies for the rest. That preserves every
   capability bit-for-bit without calling libc.
7. **Struct arguments larger than 16 bytes** are rejected at first: clang
   passes them `byval`, which forces the generic convention. Returns
   larger than 16 bytes use an sret pointer argument and are supported.
8. **The oracle for whole programs is filcc.** A corpus program is built
   twice, by nanofil (linked with filcc) and by `filcc -O0`, and must give
   the same stdout, exit status, and trap or no trap. Functions that do
   not call libc are also run through the interpreter.

**Steps:**

- **M4a. Lexer, parser, types.** *Done.* Tokens with source locations, a C11
  declaration and expression parser in DCGs producing AST terms, and type
  terms with sizes, alignments and layouts. Accept: the preprocessed
  stdio/stdlib/string/stdint/ctype headers parse, and unsupported
  constructs fail with a location.
- **M4b. Lowering of functions.** *Done.* Integer arithmetic with C's conversions,
  pointers and arrays, locals, all statements (`switch`, `goto`,
  `break`/`continue`), calls between functions in the file. Emits a Fil-C
  module checked by `valid_module`. Accept: interpreter and native results
  agree on a set of C functions called from a clang harness.
- **M4c. The rest of the ABI the C subset needs.** *Done.* External-call thunks,
  globals and string literals, function addresses and indirect calls,
  `main`. Each gets interpreter semantics too. Accept: whole programs that
  use `printf` give the same output as filcc.
- **M4d. Structs and unions.** *Done.* Layout, member access, copies, and SysV
  classification for arguments and returns of 16 bytes or less (pointer
  fields as `p`), sret for larger returns. Accept: interop tests against
  clang in both directions.
- **M4e. DCG preprocessor.** *Done.* Macros (including variadics), sysroot
  includes, conditionals, `#`/`##` and hide-set rescanning. `tests/pptest.sh`
  compares tokens with `filcc -E` on all 20 documented headers and every C
  corpus file, plus macro and location probes. The driver and C test
  scripts now preprocess `.c` themselves; `.i` input still works.
- **M4f. Corpus.** *Done.* cproc's tests and the c-testsuite, fetched by
  Nix, run in `checks.x86_64-linux.nanofil`, with every expected result
  tracked (including newly passing tests). Counts and failure triage:
  [docs/corpus.md](docs/corpus.md).

**Original deliverable:** a preprocessor and parser in DCGs, plus cproc-style
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

**Status: foundation subset complete.** Analyses, scalar simplification
and conservative exact-sized local storage are implemented,
see [docs/m5.md](docs/m5.md):
CFG, dominators, frontiers, liveness, natural loops and base-plus-offset
alias facts; `ALoc`/`AEsc` escape
classification; `promote` (mem2reg with pruned SSA phis), then conservative
SSA copy and trivial-phi elimination, behind `-O` in the driver. Bounded
symbolic queries check before/after integer returns on small functions,
including branches, loops and concrete-address memory. Every existing
suite runs again with `-O` in the Nix check; each difftest compares with the
unoptimized module. The open question is answered: analyses are pure
functions over assocs (cfg.pl). Tabled liveness is no faster than an
assoc worklist once the cost of asserting facts is counted, tabled
dominators are cubic, and incremental tabling invalidates whole tables on
small edits. Alias and loop facts are available for later passes but do
not remove checks. After copy elimination, `local_storage` keeps eligible
fixed-offset objects on the stack, including overlapping pointer/scalar
contents; uncertain uses, heap-padding accesses, returns-twice functions
and over-budget objects stay on the heap. General symbolic memory
validation remains open; the bounded integer queries are not a universal
equivalence prover.

**Deliverable:** tabled CFG, dominator, liveness, alias and loop
relations, plus SSA construction, `promote`, copy elimination and
`ALoc`/`AEsc` escape classification. Non-escaping locals stay on the
stack; escaping ones move to the heap, as Fil-C does.

**Acceptance:** each pass validated by the interpreter on the corpus, and
a symbolic before/after equivalence query on small functions. A measured
answer to the handoff's open question on versioned facts versus incremental
tabling, at realistic sizes (hundreds of blocks, small live sets).

### M6. Instruction selection and register allocation

**First slice: opt-in scalar stack caching.** `--registers=local` caches
private `w/l` frame homes within straight-line machine regions in two
audited registers. It follows instruction selection and preserves frame
layout, pointer homes, roots, helpers, phis and polls. Setjmp (even in a
dead block) and unknown machine forms retain the all-stack implementation.
Every candidate passes an independent symbolic translation checker.
`--registers=stack` remains the default and differential reference,
independent of `-O`. See [m6.md](docs/m6.md) for boundaries and measurements.

**Next:** use measured native benefit to decide whether to extend allocation
across regions or improve instruction selection. Fewer frame accesses do
not imply fewer instructions or faster execution. The earlier combined
tiling-search/CLP(Z) proposal is deferred: deterministic allocation plus
validation comes first. A solver would need reproducible limits on problem
construction, propagation and search, with a clean-state checked fallback.
Pointer allocation, root reduction, setjmp allocation and check removal
are separate safety decisions, not extensions hidden in this pass.

### M7. Check optimization and the rest of the ABI

**Deliverable:**

- Inline pointer load and store fast paths.
- Check merging per canonical pointer, using M5 alias base-plus-offset
  facts. Redundant-pollcheck removal.
- Caching global addresses across a function instead of calling the
  getter at every use (globals themselves arrive in M4c).
- Getter-free pointer-free readonly literals. This is the findings' claim,
  and it needs Oracle review and the M3 GC stress test before it ships.

**Acceptance:** fewer checks in the output than M3, the same trap behavior
on the M3 failure suite, and Oracle sign-off on each removal rule.

### M8. Demo

Compile something recognizable, such as a small ported program, with
nanofil running on Fil-C-built Trealla. Package it as
`nix build .#nanofil` with `checks.x86_64-linux.nanofil`.

### M9. Floating point

`float` and `double` through the IR, interpreter, both backends and the
C frontend, so Lua 5.4 builds with nanofil alone. The IR contract and
work order are in [docs/float.md](docs/float.md).

**Acceptance:** a `checks.x86_64-linux.nanofil-lua` check whose Lua
matches a filcc-built Lua, like the hello and zlib checks.

## Still open

- Symbolic addresses in the interpreter, for translation validation of
  memory passes (M5).
- Whether broader allocation or instruction selection justifies its cost
  (M6). CLP(Z) is deferred, not the default algorithm. Versioned facts
  versus incremental tabling was measured in M5: neither; see docs/m5.md.
- In-process execution (`tcc -run` style) needs a native host that boots
  the Fil-C runtime. It is out of scope until after M8.
- Supporting atomics and inline asm, all
  rejected until a milestone claims them.
