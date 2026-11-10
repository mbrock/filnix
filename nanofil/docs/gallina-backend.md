# The Gallina backend: a nanofil IR compiler extracted from Rocq

November 2026. A campaign plan, written before any of it is built. It
extends [the formal campaign](formal.md), which today scopes
"implementation correctness" (native lowering) out of proof. This
campaign moves the lowering itself into Rocq, so that claim comes
within reach later.

## The ambition

nanofil's middle and backend, from the IR to machine code, become
Gallina functions in the Rocq development. Extraction turns them into
a standalone nanofil IR compiler: first OCaml, then C++ through
Bloomberg's Crane, then that C++ built by Fil-C as library code a
program can call at run time.

Four things are wanted from it:

- **Speed.** The Prolog compiler spends about 650G user instructions
  on `sqlite3.c` without `-O` and about 2000G with it
  ([perf.md](perf.md), item 10). A compiler of this shape in a
  compiled functional language should need a small fraction of that.
- **A JIT component.** A program that generates code at run time,
  such as pcre2, can hand the compiler nanofil IR instead of writing
  machine code itself. The regex experiment already does this with
  the Prolog compiler, `as`, `ld` and `dlopen`; what it lacks is a
  compiler fast enough to wait for. Built by Fil-C, the compiler is
  also a memory-safe library such a program can link.
- **Less mirroring.** `Syntax.v`, `Cfg.v` and `Validate.v` transcribe
  `ir.pl` and `cfg.pl` by hand, and gates check that the two agree.
  A backend written against the model's own definitions has nothing to
  mirror, and each stage that moves lets its Prolog twin retire.
- **More proofs.** A lowering that is a Gallina function can be the
  subject of a theorem. So can a frontend that targets the IR: a
  MetaRocq extractor from typed λ□ to nanofil IR could be reasoned
  about through the IR semantics the model already has.

The C frontend stays in Prolog. It is the part that reads like C11,
and it is not where the time goes.

## What exists

### The Prolog pipeline after the frontend

Lines are `wc -l` of `nanofil/src` today. [guide.md](guide.md) walks
one function through all of it.

- **Middle end, `-O` only**: `inline.pl` 707, `promote.pl` 901,
  `copy.pl` 329, `simplify.pl` 794, `local_storage.pl` 134, with
  `escape.pl` 283, `alias.pl` 167 and `opt.pl` 154 to drive them.
  `cfg.pl` 599 gives them the CFG, dominators, loops and liveness.
- **The checked stage**: `pizlonate.pl` 267 states one check before
  each access, a `flight` for each pointer computation and a poll on
  each backward edge. `ir.pl` 2859 holds the grammar and
  `valid_module/1`. `check_reuse.pl` 1196 and its companions
  (`half_check.pl`, `schedule.pl`, `check_share.pl`) are the optional
  `--checks` evidence passes.
- **The Fil-C backend**: `filc_abi.pl` 510 plans each function's
  frame, roots, entry and exit actions and call layouts.
  `frame_slots.pl` 261 places slots. `filc_amd64.pl` 3718 emits
  instructions, access checks, function objects, data and TLS.
  `amd64.pl` 850 holds the scalar selection (`compute_op//5`) that
  `filc_amd64.pl` reuses. `asm.pl` 230 is the line terms and the AT&T
  printer.
- **Registers**: `amd64_regs.pl` 1119 allocates, and
  `amd64_regs_check.pl` 1395 with `amd64_contract.pl` 230 checks each
  allocation by translation validation.

Without `-O` the path is the **reference path**: pizlonate, validate,
`filc_abi:lower_function/5`, then `filc_amd64` with
`--registers=stack`, where every temporary lives in a frame slot, and
`asm:print_asm/1`. Its other defaults are `--checks=reference`,
`--branches=reference` and `--memcpy=call`. About 5,800 lines of
Prolog are on it, most of them in `filc_amd64.pl`.

### The Rocq model

In `nanofil/rocq/theories`, on Rocq 9.1 with stdpp and Iris:

- `Term.v` is ground Prolog terms. `Syntax.v` is the checked IR's
  core subset as inductives (`op`, `inst`, `jump`, `block`, `func`,
  the module's items). `Maps.v` is name maps and `Cfg.v` transcribes
  `cfg_idoms/2` and `dom_intervals/3`.
- `Semantics.v` is the small-step meaning (`step`, `step_rel`) over
  `Values.v`, `Memory.v`, `Ops.v` and `Ieee.v`, with the runtime as
  the module type in `Runtime.v`. `Machine.v` is the machine the
  proofs run on.
- `Validate.v` is `valid`, the validator, and `Soundness.v` proves
  `valid_no_unchecked` about it.
- `Transport.v` decodes a printed module into `Syntax.v`
  (`decode_module`); a function outside the subset stays as
  `IOutside` with its term.
- `Extract.v` already extracts `decode_module`, `judge` and
  `judge_valid` to OCaml, with zarith integers and native strings.
  `extraction/main.ml` reads Prolog canonical terms by hand, and
  `make` links `nanofil-model`.
- `rocq/gallina.pl` prints a checked module as a Gallina `term` for
  the `NAMECode.v` fixtures.

The syntax covers the checked stage only. It has no unchecked `load`
or `store`, and no vectors, `cas` and atomics, `setjmp`, `asm_fixed`
or `touch`. Of Lua 5.4.7, every function but one decodes into it.

## The first version

The first version is the reference path and nothing else:

1. the asm line terms and their printer;
2. the frame and ABI plan;
3. stack-homed emission for the model's core subset;
4. pizlonation, with the model's `valid` between it and emission.

It reads IR and writes assembly text for GNU as, the same text the
Prolog reference emission prints.

It leaves out:

- the whole middle end (inline, promote, copy, simplify, local
  storage, escape and alias analysis);
- the check-reuse passes, and emission of the reuse forms they make
  (`renew`, `half_check`, `check_limit` and the rest);
- the `amd64_regs` allocator, its two checkers and the `temps` and
  `pointers` modes, with `--operands`, `--branches=selected`,
  `--memcpy=inline` and `--share`;
- plain (non-Fil-C) mode, and every construct outside `Syntax.v`'s
  subset. A module with an `IOutside` function is refused, and the
  Prolog compiler compiles it as before.

**"The fast simple register mode", as I read it.** Prolog has three
register modes today: `stack`, `temps` and `pointers`. Only `stack`
is simple, and it is the reference every other mode is checked
against, so the first version ports `stack`. A register allocator
that is fast and simple by design (one pass, block-local or linear
scan, no translation checker because it is proved instead) is its own
later milestone, M7. It is not a port of `amd64_regs.pl`: that
allocator and its checkers are half of `-O`'s compile time.

## Reusing the model's definitions

The backend imports the model; it does not copy it.

- The input type is `Nanofil.Syntax.func`. There is no second
  inductive for the checked IR. `class`, `width`, `op`, `value`,
  `inst`, `jump` and the data items are the ones `Semantics.v` gives
  meaning to and `Validate.v` judges.
- Names are `Term.name`, maps are `Maps.v`, block order and dominators
  are `Cfg.v`, and decoding is `Transport.decode_module`.
- The pipeline calls `Validate.valid` itself. Its theorem then speaks
  about exactly the module the backend lowers.
- What is new belongs to the backend alone: asm lines and operands,
  frame plans, and the emission functions.

The new files live in their own project, `nanofil/rocq/backend/`,
with `-R ../theories Nanofil` and `-R . Backend`, on the pattern of
`rocq/spikes`. Its Nix check compiles against the model's compiled
theories and is not part of the quick `nanofil-rocq` gate, so that
gate does not grow. It touches no file of the program logic or the
libc contracts.

Two places need more than the model has, and both go to the model's
owner as requests instead of being worked around:

- **The unchecked stage.** Pizlonation's input has `load`, `store`
  and unproven calls. Recommendation: a backend-owned `Unchecked.v`
  that reuses `class`, `value`, `op` and `jump` and adds only the
  unchecked instruction forms, so `Syntax.inst` and every proof by
  cases over it are untouched.
- **Constructs outside the subset.** Vectors, atomics, `setjmp` and
  fixed-register asm reach the backend only when `Syntax.v` and the
  semantics gain them. The backend never invents a private
  constructor for one.

## Checking it against the Prolog compiler

The Prolog reference emission is the oracle, and the standard is
**byte identity**.

- **Per stage.** Each ported stage gets a Prolog command that prints
  its output as canonical terms: the asm lines, the frame plan, the
  pizlonated module. The extracted stage must produce the same terms,
  or the same text.
- **End to end.** For every module of the corpus, the assembly from
  the extracted compiler equals `nanofil compile`'s. The corpus is
  what exists: `tests/filc/*.ir`, `tests/c`, `tests/c/prog`, random
  modules from `tests/gen.pl` by seed, and the whole programs (hello,
  zlib, bzip2, Lua, SQLite).
- **By behaviour.** `difftest.sh` and `progtest.sh` run with the
  extracted backend swapped in, for the day the two are allowed to
  differ.
- **Coverage is reported, not assumed.** Each run prints how many
  functions were compiled, and how many modules were refused for an
  `IOutside` function.

Byte identity holds until the Gallina backend is the reference. From
then on a stage's Prolog twin is retired instead of kept in step, and
that is where the mirroring goes away.

The quick subset of these tests runs in the backend's own Nix check.
The large programs run in the package checks, which already exist and
already run after a push.

## Extraction

**OCaml first.** It is the extraction Rocq ships, the model already
uses it, and the driver, zarith and the Nix build are in place. The
compiler's entry points are Gallina functions from text to text, so
the OCaml driver only reads a file and writes one. Text is built as
lists of parts and joined once, as `asm.pl` does: SQLite's assembly
is about 100 MB.

**Then Crane.** [Crane](https://github.com/bloomberg/crane) is a Rocq
plugin forked from the OCaml extraction. By its README it emits C++23
that needs no runtime system and manages memory with `shared_ptr`,
is LGPL-2.1, installs against Rocq 9.0 and is under active
development with parts still experimental. Known risks, each settled
in M6 before anything depends on it:

- our pin is Rocq 9.1.1, so the plugin may need porting or a second
  Rocq in the build;
- arbitrary-precision `Z` needs a C++ home (a small bigint, or
  checked fixed-width integers where a bound is proved);
- reference counting has a cost OCaml's collector does not, and
  deep recursion over long lists needs care in C++ as it did in
  OCaml (`Extract.v` records one such overflow).

**Crane is an alpha, and we expect to patch it.** Its site says so,
and it will not take all of Gallina. Three rules follow.

- The backend stays in a plain subset: first-order inductives,
  structural fixpoints, `list`, `option`, `Z`, strings and records.
  No coinductives, no universe polymorphism, no type classes or
  functors on the extracted path, and no local fixpoint that is
  mutually recursive with its enclosing function (Crane's manual
  lists that shape among those its loop transform declines). The
  OCaml extraction does not care, and any second extractor will.
- Crane's own switches are tried first. Its reference manual has
  type mappings (`Crane Extract Inductive`), `Set Crane Arena` for
  region allocation of recursive fields, `Set Crane NonAtomicRc`
  for a non-atomic count in place of `shared_ptr`, `Set Crane Reuse`
  for in-place reuse and `Set Crane Loopify` to turn recursion into
  loops. A compiler that runs once per module or per pattern and
  then frees everything is the case arenas are made for.
- Past the switches, it is our fork. A change to what Crane emits
  is a patch in a set we own, applied by the Nix build to a pinned
  Crane revision, and offered upstream where it is general. The
  differential tests are what keep a patched extractor honest: the
  C++ build must print the same bytes as the OCaml build.

**The fallback is Gallina to C.** If Crane costs more to bend than
it saves, CertiRocq (formerly CertiCoq) compiles Gallina to Clight,
which any C compiler takes, and brings a small C runtime with its
own collector; the Codegen plugin is a second, narrower route to C.
Either gives C that filcc can build, so the library and JIT steps
below do not depend on Crane. Neither is tried unless M6 fails, and
whether CertiRocq's runtime (its tagged values and its collector)
is at home under Fil-C is the first thing to find out then.

The Gallina is written with the second extraction in mind from the
start: no OCaml-only `Extract Constant` on a hot path without a C++
twin, and no hand-written OCaml that the compiler's result depends
on. The canonical-term reader in `main.ml` is such code today, and M4
replaces it with a Gallina one.

## The path to a Fil-C library and a JIT

The first JIT needs no encoder and no new way to load code. The
regex experiment
([its README](../../experiments/regex-nanofil/README.md),
[pcre2-jit.md](../../docs/pcre2-jit.md)) already runs one. Behind
`pcre2_jit_compile`, a patched libpcre2 prints a pattern's bytecode
as terms and runs a compiler, `rxc`, on a cache miss. The
experiment's regex compiler, itself Prolog, turns the terms into
unchecked nanofil IR, then `rxc` runs `nanofil -O compile`, `as` and
`ld -shared`. The library loads the shared object
with `dlopen` and keeps it in a cache directory. The Fil-C runtime
the code calls is already in the loading process, so the trusted
runtime does not change.

What that route lacks is a fast compiler. A miss costs 0.15 to 0.8 s
per pattern on SWI-Prolog, and nearly all of it is `nanofil -O
compile`: `as` and the link together take under a tenth of a second
even for a module of 36 functions. On Fil-C Trealla, which is what a
libpcre2 with its compiler inside would run, the median is 2.4 s.
sljit takes 0.1 ms. So the steps are:

1. **The extracted compiler in `rxc`.** `nanofil-backend compile`
   takes the place of `nanofil -O compile`. The regex compiler
   emits unchecked IR, so this needs pizlonation (M4) and nothing
   after it. The regex compiler itself stays Prolog for now (0.07 s
   for 36 patterns).
2. **Code worth running.** The first version's code is what Prolog
   makes without `-O`, which the experiment measured at 5 to 10 times
   slower than `-O` code. That is about the interpreter's speed on
   some patterns, so the route is not yet worth switching on. With
   `-O`'s middle end and check passes but stack homes, the code is
   only 1.1 to 1.7 times slower than full `-O`. So for pcre2 the
   check passes matter far more than a register allocator. M5
   measures which of them buy the difference on the regex compiler's
   IR, and those are ported first.
3. **`libnanofil`, pizlonated.** Crane's output is plain C++23, and
   Fil-C is a C++ compiler (clang 20 with libc++), so the extracted
   compiler is built with filcc and given a C interface: IR text or
   a term tree in, assembly text out. libpcre2 links it and calls it
   in the process; the hook still runs `as` and `ld` and loads with
   `dlopen`. It is memory-safe against any input, by Fil-C, and
   checked by the same differential tests as the OCaml build.
   Crane's README asks for Clang 19 or later; whether Fil-C's libc++
   has everything the output uses is found out in M8.

Two further steps are options for later, taken only if measurement
asks for them:

- **An encoder and a shared-object writer** in Gallina, in place of
  `as` and `ld`, checked against them byte for byte. The result is
  still loaded with `dlopen`, so this too leaves the runtime alone.
  It removes two process starts per miss and the need for binutils
  where the program runs.
- **Installing code in the process**, without a file. Fil-C's `mmap`
  refuses `PROT_EXEC`, so a program cannot run bytes it wrote. The
  pinned staging runtime has one JIT (`filc_llvm_jit.c`,
  `filc_llvm_jit.h`), which compiles LLVM IR built through a curated
  C API and places the code in its own heap; it loads LLVM into the
  process and is refused to setuid programs. A nanofil entry of that
  kind would be a change to the trusted runtime. It would get a
  design note and an Oracle review before any code, and it is
  mbrock's decision.

The `dlopen` route trusts the cache directory, as the experiment's
README says: what is in it is loaded as code. The validator is the
asset on the compiler's side. `valid` is already Gallina, already
extracted and already proved (`valid_no_unchecked`), so the compiler
checks a client's IR after pizlonation and before emitting anything.

## Performance targets

These are targets, not measurements. M1 measures the baseline per
stage; until then the known figures are perf.md's:

- `sqlite3.c`, 3106 functions and 218k checked instructions: 651.6G
  user instructions without `-O`, about 2000G with it. In a loaded
  run emission was 33 s of the plain compile and 151 of 269 s at
  `-O`.
- Across 909 translation units, `-O` costs 2.17× plain.

Targets, each measured in `perf stat` user instructions on the same
input and the same stages:

- **OCaml, M3**: the ported stages take at most a twentieth of the Prolog
  stages' instructions on `sqlite3.c` and on `lvm.c`.
- **OCaml, after M5**: at most a fiftieth, with checked IR to assembly for
  all of SQLite inside 10G instructions.
- **Crane C++**: within 2× of the OCaml build.
- **Pizlonated**: within 4× of the unsafe C++ build, the top of
  Fil-C's usual range.
- **As pcre2's compiler**: IR to assembly for one pattern in at most
  10 ms, against 0.15 to 0.6 s in Prolog, so that a miss is bounded
  by the regex compiler, `as` and `ld` at about a tenth of a
  second. The code's speed has its own target once M5 has measured
  the passes: within 2× of `-O` code on the experiment's nine
  benchmark patterns.

A stage that misses its target gets a profile and a note of where
the time goes before the next stage starts.

## Milestones

Each ends with its gate green and a short note of what it found.

**M0. The plan and the project.** This document. `rocq/backend/`
with its `_RocqProject`, a build script, extraction to a
`nanofil-backend` binary and a Nix check outside the quick gate.
Gate: the empty project builds, extracts and passes `parse.sh`.

**M1. Asm lines and the printer.** `Asm.v`: lines, directives,
operands and expressions as inductives, a decoder from terms, and
the printer. A Prolog command prints a module's line list as terms.
Gate: for the corpus, the printed text equals `nanofil compile`'s,
byte for byte; the per-stage baseline is measured and recorded here.

**M2. Frames and the ABI plan.** `filc_abi.pl` and `frame_slots.pl`:
slots, roots, entry and exit actions, call layouts, signatures.
Gate: the plan of every corpus function in the subset equals
Prolog's, as terms.

**M3. Stack-homed emission.** `filc_amd64.pl`'s reference emission
and `amd64.pl`'s scalar selection, in pieces: scalars, compares and
jumps first; then checks, flights, raw accesses and polls; then
calls, variadics, function objects, data, aliases and TLS. Gate:
whole-module byte identity on the corpus, hello, zlib and Lua, with
the first performance target.

**M4. Pizlonation and a standalone compiler.** `Unchecked.v`,
`Pizlonate.v` and a Gallina reader for IR text. The pipeline is
read, pizlonate, `valid`, lower, emit, print. Gate: the pizlonated
module equals Prolog's as a term, and `nanofil-backend compile
FILE.ir` equals `nanofil compile FILE.ir` with no Prolog in the
pipeline.

**M5. Speed, and pcre2 through `rxc`.** Profile, fix data
structures, record the numbers in perf.md's style. `rxc` gets a
switch that runs `nanofil-backend` in place of the Prolog compile.
Gate: the second performance target; the experiment's checks pass
with the extracted compiler; the miss time and the code's speed are
recorded, with a list of the `-O` passes that code needs.

**M6. Crane.** Build Crane in Nix against our Rocq, extract the same
entry points to C++, compile with clang++ and run the same
differential tests. Gate: byte identity again, and the C++ target.
If Crane cannot extract the development, the note says what stopped
it, and the order of remedies is: change the Gallina, use a Crane
switch, patch Crane, fall back to CertiRocq.

**M7. A fast simple register allocator.** Designed for a proof, not
ported. Gate: difftests and package checks by behaviour, and a
measured run-time gain over stack homes on the benchmark gate.

**M8. The Fil-C library.** The Crane output built by filcc as
`libnanofil` and called in the process by the pcre2 hook, which
still runs `as` and `ld` and loads with `dlopen`. Gate: the
pizlonated library passes the differential tests and the
experiment's checks.

**M9. Hybrid `-O`.** Emission of the reuse forms, so Prolog's middle
end and check passes can feed the extracted backend. This is where
users of `-O` first feel the speed.

**Later.** The middle end and the check passes in Gallina, each
replacing a `*_refines` run-time check with a theorem, the ones
pcre2's code needs first. An encoder and a shared-object writer, and
installing code in the process, if measurement asks for them.

M1 to M3 can run in parallel once M1's `Asm.v` types are fixed,
because the plan and the emission pieces own different files.

## The proofs it enables

None of these is promised by the milestones above. They are what
becomes statable.

- **Pizlonation is valid.** `valid (pizlonate m) = Some true` for
  every well-formed unchecked module. With `valid_no_unchecked` it
  says no pizlonated module ever runs unchecked, with no validator
  run in the trust path.
- **Structural facts about lowering.** Frame slots do not overlap.
  Every pointer live across a poll or a call is a root. A check's
  emitted sequence branches to a trap exactly when the model's
  `Check` fails.
- **Implementation correctness.** A semantics for the asm subset the
  backend emits, and a simulation from `step_rel` to it, one
  instruction kind at a time, starting with scalar selection against
  `Ops.v`. This is the row formal.md leaves out of proof today.
- **Proved passes instead of checked ones.** A register allocator or
  a check-reuse pass with a refinement theorem needs no translation
  checker at compile time, which is where half of `-O` goes.
- **A λ□ extractor.** MetaRocq erases Rocq terms to λ□, with a
  proof for the untyped erasure and a typed variant that keeps
  types. A compiler from λ□ to nanofil IR, written in
  Gallina, would have a correctness statement in terms of
  `Semantics.v`, and its output would need no collector of its own,
  because Fil-C's is underneath. At the end of that road the
  extracted backend compiles itself to nanofil IR, and neither OCaml
  nor C++ is between the Gallina and the machine code.

## Decisions wanted

Each has a recommendation; work proceeds on it unless told
otherwise.

1. **What the first version's register mode is.** Recommended: stack
   homes now, a new simple allocator at M7, never a port of
   `amd64_regs.pl`.
2. **Where the compiler starts.** Recommended: checked IR first (M1
   to M3), since that is what `Syntax.v` describes, then pizlonation
   on a backend-owned `Unchecked.v` (M4).
3. **Byte identity as the standard**, until the Gallina backend is
   the reference. Recommended: yes; it is the cheapest strong test
   there is, and the snapshot gate already works this way.
4. **The first JIT is the regex experiment's route**: `as`, `ld
   -shared` and `dlopen`, with the extracted compiler in `rxc` from
   M5. Settled by mbrock. An encoder and installing code in the
   process are later options; the second is a runtime change and
   would wait for its own review.
5. **What pcre2 needs after M5.** The first version's code has none
   of `-O`'s check elimination. Recommended: port the check passes
   M5 finds decisive before the M7 allocator, since the experiment
   shows they are worth 5 to 10× and registers 1.1 to 1.7×.
