# nanofil plan

nanofil is a C compiler and an executable account of capability semantics,
written in Prolog. Its own IR (`src/ir.pl`, interpreted by `src/interp.pl`
and printed by `src/ir_text.pl`) makes object identity, address/capability
propagation, access requirements and runtime effects explicit. Its x86-64
assembly links with clang-built Fil-C code for the documented subset.

The foundation is [docs/campaign.md](docs/campaign.md): separate safety
obligations from the evidence that discharges them and the code that
implements them. Runtime checks are the reference implementation, not the
only possible justification. Semantic investigation is a purpose of the
compiler, not a testing accessory. Broad LLVM-style optimization is not
the goal, and neither a verified compiler nor a certificate system is
claimed to exist today.

This file tracks milestones; their numbering records the project's
history, not a requirement to finish general register allocation before
semantic work. [docs/handoff.md](docs/handoff.md) is the original proposal,
kept as written. [docs/abi-findings.md](docs/abi-findings.md) records what
was checked against the pinned toolchain and takes precedence over it.

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
   unit (docs/m4.md). So are VLAs and variably modified types: an
   `alloc` of the run-time size where the declaration is reached, and
   lengths evaluated where C evaluates them (docs/m4.md).
   Direct setjmp-family calls and ordinary longjmp calls are now supported
   in Fil-C mode; see [docs/setjmp.md](docs/setjmp.md). `__atomic_load_n`
   and `__atomic_store_n` are supported, pointers through Fil-C's atomic
   helpers ([`90fe17c`](https://github.com/mbrock/filnix/commit/90fe17c)),
   and the empty asm barrier is accepted; other inline asm, `_Atomic`
   and `_Complex` are still refused.
7. **Relationship to [experiments/sarcasm-prolog](../experiments/sarcasm-prolog/README.md).**
   It is related but separate. That experiment translates assembly to C and
   lets clang apply Fil-C. nanofil emits the Fil-C ABI itself. nanofil
   adopts its rules for extending (see below) and its habit of documenting
   the supported subset alongside each Nix check, but shares no code.

## Rules for extending

- State each transformation's input/output contract, effects, evidence
  and preservation claim. Keep safety of checked execution, behavioral
  refinement and correctness of native lowering as distinct obligations.
- Compare before/after executions with the M1 interpreter where modeled,
  and with native interop/GC tests where effects are abstracted. Bounded
  symbolic searches and tests support universal claims; they do not
  discharge them. Unknown execution or exhausted fuel is inconclusive.
- Remove a safety check only when its obligation has an accepted
  justification under explicit rules. An analysis, annotation or AI
  proposal does not authorize its own result. Failure, resource limits
  or unsupported evidence keep the reference checks or reject compilation.
- Check motion requires a stated policy for failure timing and effects.
  Upstream's permission to fail earlier on violating executions is not
  automatically nanofil's. Preserve current behavior until a different
  contract and its validation have been explicitly reviewed.
- Keep the unoptimized path selectable and use it as the differential
  reference for each optimization. Give transformations independent
  computational identities, as `optimize_pass/3` does, without imposing
  microscopic passes or a generic framework.
- Purity wherever it pays (handoff, "Lessons from The Power of Prolog").
  Use explicit terms, mode contracts and ordinary relations; ground
  compiler walks need not run backwards. Keep I/O and search budgets out
  of semantic rules. See AGENTS.md for the measured host tradeoffs.
- Changes to what is considered safe (check elimination, rooting, getter
  skipping) get an Oracle review first, as for the compiler itself
  (root AGENTS.md).

## The executable foundation is in place; general proofs are not

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
validated scalar stack cache, and M7 an opt-in, forward reuse of
heap check evidence; general register allocation and broader check
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
[docs/m4.md](docs/m4.md) and [docs/corpus.md](docs/corpus.md). The
corpus has no rejections left: all 262 programs with a `main` that
filcc builds pass. Real programs built with nanofil alone, each a Nix
check compared with a filcc build:

| Check | Program | Added in |
| --- | --- | --- |
| `nanofil-hello` | GNU hello | [`e8d4524`](https://github.com/mbrock/filnix/commit/e8d4524) |
| `nanofil-zlib` | zlib | [`5d2ac42`](https://github.com/mbrock/filnix/commit/5d2ac42) |
| `nanofil-lua` | Lua 5.4 | [`d1ba1ee`](https://github.com/mbrock/filnix/commit/d1ba1ee) |
| `nanofil-bzip2` | bzip2 1.0.8 | [`9987a8c`](https://github.com/mbrock/filnix/commit/9987a8c) |
| `nanofil-lz4` | lz4, unpatched | [`bf0e86d`](https://github.com/mbrock/filnix/commit/bf0e86d), [`ab05a5b`](https://github.com/mbrock/filnix/commit/ab05a5b) |
| `nanofil-sqlite` | SQLite 3.51.2 with FTS5 | [`715c737`](https://github.com/mbrock/filnix/commit/715c737) |
| `nanofil-sed` | GNU sed 4.10 (gnulib) | [`cda56e6`](https://github.com/mbrock/filnix/commit/cda56e6) |
| `nanofil-jq` | jq 1.8.2 with oniguruma, decNumber | [`cda56e6`](https://github.com/mbrock/filnix/commit/cda56e6) |
| `nanofil-dash` | dash 0.5.13 | [`cda56e6`](https://github.com/mbrock/filnix/commit/cda56e6) |
| `nanofil-xz` | xz-utils 5.8.4, threaded coders at 1 to 8 threads | [`41da3be`](https://github.com/mbrock/filnix/commit/41da3be) |

Since the steps below were planned, M4 gained VLAs and variably
modified types ([`4822471`](https://github.com/mbrock/filnix/commit/4822471)),
GNU packed layout, range designators, struct arguments over 16 bytes
by value ([`1d1b22c`](https://github.com/mbrock/filnix/commit/1d1b22c)),
float-containing structs and aggregate `va_arg`
([`b6c1cc6`](https://github.com/mbrock/filnix/commit/b6c1cc6)), atomic
builtins, a C23 mode and the GNU extensions gnulib uses
([`36039eb`](https://github.com/mbrock/filnix/commit/36039eb)).
Refused with a message: `_Complex`, `_Atomic`, K&R definitions, inline
asm other than the empty barrier (in a function that is compiled),
GNU case ranges, alignment stronger than natural except up to 16 on a
struct or union definition, vector types, `_Float16` and `__bf16`,
pointer-to-`bool` in static initializers, variable and
variadic function aliases, and long double classification other than
by sign ([docs/m4.md](docs/m4.md), *Linux userland additions* and *xz
additions*). Constructors and destructors run as clang's do
([`41da3be`](https://github.com/mbrock/filnix/commit/41da3be)).
`_Thread_local` and `__thread` variables are per-thread objects, created
lazily through clang's getter protocol and interoperating with clang's
([docs/abi-findings.md](docs/abi-findings.md), *Thread-local variables*).

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
   any use of a float value is rejected. *Superseded by M9.*
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
7. **Struct arguments larger than 16 bytes** were rejected at first:
   clang passes them `byval`, which forces the generic convention. They
   are now passed as their eightbytes, and a function taking one is
   generic-only, promoting its packet like a variadic function
   ([docs/abi-findings.md](docs/abi-findings.md), *Byval arguments*).
   Returns larger than 16 bytes use an sret pointer argument.
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

**First slice: opt-in scalar stack caching and immediate selection.**
`--registers=local` selects integer immediate arithmetic and shifts, then
caches private `w/l` homes in two registers within straight-line regions.
Frame layout, pointer homes, roots, helpers, phis and polls stay unchanged.
Setjmp (even in a dead block) retains reference selection and no caching;
unknown machine forms retain selected-but-uncached code. The independent
symbolic checker validates caching, not the preceding instruction selection.
`--registers=stack` remains the default and differential reference,
independent of `-O`. See [m6.md](docs/m6.md) for boundaries and measurements.

**Next:** [docs/perf.md](docs/perf.md) profiles `-O` against filcc `-O2`
with a benchmark gate and ranks the code-quality work: switch dispatch,
branch selection, whole-function scalar allocation, inlining, then the
items that need safety review. Use measured native benefit to decide whether to extend allocation
across regions or improve instruction selection. Fewer frame accesses do
not imply fewer instructions or faster execution. This is a separate
workstream, not a prerequisite for the semantic agenda. The earlier combined
tiling-search/CLP(Z) proposal is deferred: deterministic allocation plus
validation comes first. A solver would need reproducible limits on problem
construction, propagation and search, with a clean-state checked fallback.
Pointer allocation, root reduction, setjmp allocation and check removal
are separate safety decisions, not extensions hidden in this pass.

### M7. Safety obligations and alternative evidence

**Status: first deliverable done ([docs/m7.md](docs/m7.md)), in two
rounds: block-local
([`57cacd6`](https://github.com/mbrock/filnix/commit/57cacd6)) and across
CFG edges ([`d9883ed`](https://github.com/mbrock/filnix/commit/d9883ed)).** An opt-in
pass (`--checks=reuse`, off by default) lets a heap check's proof cover
later scalar accesses through the same pointer, in its block and
forward along CFG edges (intersected at joins), until a call,
allocation, pointer store, getter, poll edge or other non-preserving
instruction, or a redefinition. The validator, emitter and an
independent refinement check accept the result by separately stated
rules; the interpreter's raw accesses already re-check against current
object state. Every check still sits at its first access, so traps keep
their timing and reasons. Oracle reviewed the design before
implementation and the result after, for each of the two rounds. It
removes 17.7% of emitted heap checks on the C corpora without `-O`, 5.2%
with it. Measured natively on zlib, bzip2, lz4 and Lua, it saves up to
6.4% of run time without `-O` and nothing measurable with it
([`3576b51`](https://github.com/mbrock/filnix/commit/3576b51)). The
hello, zlib, Lua, bzip2, lz4 and SQLite checks also build with
`--checks=reuse` and must match filcc.

**First deliverable:** one narrowly specified alternative to repeated
runtime checking, such as reuse for repeated scalar accesses in a
straight-line region. State the facts, transfer and merge rules,
invalidation effects and independent acceptance rule. Preserve the
reference path and current behavior; keep checks for unproved conditions.
The [campaign](docs/campaign.md#the-next-work-extends-evidence-not-an-optimizer-framework)
sets the work order and proof boundaries.

**Acceptance:**

- An explicit reviewed IR/validator/interpreter/emitter contract, including
  the identity and lifetime of evidence. No unchecked assertion of safety.
- Before/after outcomes within the oracle's domain, including existing
  trap distinctions; tests that reject stale, wrong-object, branch-only
  and insufficient-rights/range evidence. Plant plausible invalidation
  and coverage mistakes and require the tests or checker to reject them.
- Native and GC/helper-effect coverage for what the oracle abstracts.
  Fewer emitted checks and measured costs are useful outcomes, not proofs.
- A selectable transformation and its actual output in the playground.
  Show explanatory evidence only when it is a real compiler product.

**Later, separate contracts:** split spatial and temporal facts for broader
motion, infer capabilities through integer dataflow, or formalize a small
validation rule. AI-assisted discovery may propose proofs or replacements;
acceptance must remain reproducible and independent of the proposing agent.
No theorem prover or certificate format is chosen yet.

Poll removal, getter caching, getter-free literals and broader local
storage remain separate runtime/rooting decisions. None follows merely
from having proved an access range or from an existing M6 cache check.

### M8. Demo

Compile something recognizable, such as a small ported program, with
nanofil running on Fil-C-built Trealla. Package it as
`nix build .#nanofil` with `checks.x86_64-linux.nanofil`.

### M9. Floating point

**Status: done.** `float` and `double` are IR classes `s` and `d`, and
Lua 5.4 builds with nanofil alone
([`d1ba1ee`](https://github.com/mbrock/filnix/commit/d1ba1ee)). x87
`long double` is a further class `x` with real 80-bit semantics in the
interpreter and both backends
([`ab05a5b`](https://github.com/mbrock/filnix/commit/ab05a5b)); it is
stored, passed, returned and promoted in variadic calls as clang does,
which closed c-testsuite `00204` and lets lz4 build unpatched.
[docs/float.md](docs/float.md) is the contract. `_Complex` is refused.

`float` and `double` through the IR, interpreter, both backends and the
C frontend, so Lua 5.4 builds with nanofil alone. The IR contract and
work order are in [docs/float.md](docs/float.md).

**Acceptance:** a `checks.x86_64-linux.nanofil-lua` check whose Lua
matches a filcc-built Lua, like the hello and zlib checks.

## Still open

- The observation relation for semantic transformations: object identity
  correspondence, failure timing and effects, beyond today's outcome
  comparison. Checked-IR safety and native correctness need separate claims.
- The first independently checked alternative evidence for an access,
  and a small formalization connected to the actual executable semantics.
- Symbolic addresses in the interpreter, for translation validation of
  memory passes (M5).
- Whether broader allocation or instruction selection justifies its cost
  (M6). CLP(Z) is deferred, not the default algorithm. Versioned facts
  versus incremental tabling was measured in M5: neither; see docs/m5.md.
- In-process execution (`tcc -run` style) needs a native host that boots
  the Fil-C runtime. It is out of scope until after M8.
- `_Atomic` types, `__atomic` builtins beyond load and store, and inline
  asm other than the empty barrier, all refused until a milestone claims
  them.
