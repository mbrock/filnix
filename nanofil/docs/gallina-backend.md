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
  The speed is wanted for JIT use and for very large files, not for
  everyday C builds; the scope note below says why.
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

**Scope: the C frontend stays in Prolog.** That is not because it is
cheap. Measured at M1, the frontend is about 40% of the plain SQLite
compile, and 325 of the 347 s the 281-module test corpus takes,
because headers dominate an ordinary translation unit. So a perfect
backend barely speeds up everyday C compiles.

The campaign's speed goal serves two other uses:

- JIT use, such as pcre2 patterns compiled from IR, where there is
  no C to parse and the backend is the whole compile;
- very large files, where the backend is more than half of it.

The scope is mbrock's, and so is the reason: "i excluded the c
frontend from the campaign scope mostly because it's big and messy
and i am kinda mostly driven to do all this from thinking about jit
etc". The frontend is something to reconsider later, outside this
campaign.

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
- `rocq/scripts/gallina.pl` prints a checked module as a Gallina `term` for
  the `NAMECode.v` fixtures.

The syntax covers the checked stage only. It has no unchecked `load`
or `store`, and no vectors, `cas` and atomics, `setjmp` or
`asm_fixed`. Of Lua 5.4.7, every function but one decodes into it.

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
  and unproven calls, which `Syntax.inst` does not have. It gets no
  types of its own: pizlonation rewrites the module's term, as
  pizlonate.pl does, and the model's decoder reads the result. So
  `Syntax.inst` and every proof by cases over it are untouched, and
  nothing mirrors them. M4 says why.
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

M6 met all three, and its record under [Milestones](#milestones)
says how each was settled.

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
on. The canonical-term reader in `main.ml` was such code. Since M4
the standalone compiler reads IR text with `IrText.v`, and the
OCaml reader serves only the gates that take Prolog's terms. Three
character primitives of `IrText.v` have OCaml definitions. At M6
they needed no C++ twins of their own: Crane's mappings of
`nat_of_ascii`, `ascii_of_nat` and `string_of_list_ascii` cover
them.

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
   makes without `-O`. M5 measured it on the experiment's nine
   benchmark patterns: 2.7 to 16 times slower than `-O` code, 6.2
   times in the geometric mean, and still 1.5 to 3.5 times faster
   than PCRE2's interpreter. The regex compiler keeps a node's
   choice state in `alloc` slots, and without promotion every use of
   one is a checked load or store. Promotion, copy propagation and
   the selection of branches bring the code to 2.1 times `-O`'s,
   which is all that `-O` gives with stack homes; registers are the
   other 2 times. Simplification, inlining, the check passes and the
   inline `memcpy` change nothing for this code. M5b ported the first
   three, before Crane and before the allocator, and `rxc` now runs
   `nanofil-backend compile-promoted`: the measured figure is 2.10.
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

These are targets. The figures known before the campaign are
perf.md's:

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

**The baseline, measured at M1.** CPU seconds of the plain compile
in SWI-Prolog, stage by stage, on one core of an orb (a 2.6 GHz
Xeon):

- SQLite 3.51.2's amalgamation with `nix/sqlite.nix`'s flags,
  preprocessed: 141,500 lines in, 5.52 million asm lines and 135 MB
  out. Frontend 35.9, pizlonate 6.3, validate 13.6, emit 20.6,
  print 12.8. The stages this campaign ports are 53.3 of 89.2 s.
- The 281 modules of the test corpus together: frontend 325.5,
  pizlonate 2.3, validate 5.6, emit 9.9, print 3.2. Their headers
  dominate, so the corpus tests sameness and SQLite tests speed.
  With the frontend at 94% of the corpus's time, no backend makes
  those compiles much faster.

At M1 the extracted printer printed SQLite's lines in 5.0 s, which
is 2.5 times Prolog's speed, within 230 MB. Two things follow:

- Printing is where Prolog is nearest to native code, because SWI
  writes its text in C. The Gallina printer makes a string per digit
  and a list cell per part. So this ratio says little about emission.
- A twentieth of 53.3 s is 2.7 s, and the printer alone takes 5.0.
  The M3 target cannot be met unless the printer gets faster too, so
  M3 profiles it first and M5 owns what remains.

**The profile, at the start of M3.** `perf record` with DWARF call
graphs, on SQLite, in CPU seconds: an orb has no hardware counters,
so instructions are not counted here. The targets for the two parts
are a twentieth of Prolog's stages: 0.64 s for printing, and 1.0 s
for the plans and the emission together.

The printer went from 5.0 s to 1.1 s:

- To 2.1 s by reading 64 lines at a time and not 4096. The terms,
  lines and parts of a large chunk outlived OCaml's 2 MB minor heap
  and were copied to the major one. This was the driver's fault and
  not the printer's.
- To 1.8 s in `decimal`. The extracted code builds a number or a
  list written inside a function again at each call, so every digit
  built the number 10 three times and the list of ten digits once.
  They are definitions of their own now. The bound on the digits
  was the count of the number's bits, taken a bit at a time; it is
  18 for numbers below 10^18.
- To 1.5 s with one division per digit, and with zarith's
  conversions between `Z` and `nat` where the stdlib's count by
  ones.
- To 1.1 s by filling a buffer per chunk; each part was a write.

What remains is a list cell per part and a string per digit.

The plans went from 7.8 s to 2.6 s:

- To 3.7 s by taking OCaml's hash of a string for a name's bucket,
  as the model's extraction does. The Gallina hash is eight integer
  operations per character.
- To 2.6 s with a 32 MB minor heap in the gate.

Of what remains, liveness is a third, the first and last touch of
each temporary a quarter, the fusing of checks a fifth, and the
lowering of instructions a tenth. No one function stands out. About
half of all of it is finding and adding names in maps: a name is a
term such as `tmp(v12)`, hashed and compared as one at every step.
The repair is to number a function's temporaries once and key the
maps and sets by number, which changes every pass of M2 and belongs
to M5. The gate's 1.4 GB for SQLite is nearly all the module read
as terms, which a reader of NFB words would not build.

Both parts still miss their targets, by less than twice for
printing and by more than twice for the plans before any emission.
M3's emission is written with this in mind, with no number or list
written inside a loop.

**The profile, at the end of M3.** The same tool on
`nanofil-backend module`, which reads SQLite's module, lowers it,
emits it and prints it in 8.8 s. As shares of that time:

- Reading the module as terms is 28%, and nearly two thirds of
  that is the collector. A reader of NFB words builds the module
  with no terms between; it becomes the compiler's input once it is
  faster than reading text.
- Building the plans is 24%. Slots are 16%, nearly all of it the
  first and last touch of each temporary (15%) and the liveness
  under that (8%); fusing is 5%. This is the part that waits for
  numbered temporaries.
- Emitting the functions is 12%: 7% for the instructions' lines
  and 4% for a function's context, which builds maps keyed by a
  name's term. Data and thunks do not show.
- Printing is 12%.
- The collector is 27% of everything, the minor one 15% and the
  major one 12%.

Inside the instructions' lines no one form stands out. The leaves
are string concatenation (17%), the hash and comparison of a name
(about 40% with the maps' lookups), and list append (10%). So the
emission's own cost is names again: a slot is found by the term of
its temporary, and a label is built from strings at each use.
Numbered temporaries remove the first, and a label kept as parts
until it is printed removes the second.

**The measurements of M5.** On the standalone compiler, which
compiles SQLite's IR text in 41 s where `nanofil compile` takes 70.

*The validator is the cost.* The model's `valid` is 18 to 20 s of
the 41, where Prolog's own validator takes 14. It grows with the
square of a function's definitions: two thirds of it is in three
functions of 6,000 to 14,800 definitions.

- `single_definitions` is 7.0 s. For each definition it filters the
  list of all of them.
- The reuse forms' stage is 5 to 6 s more, and the blocks' own
  rules 4.2 s. Both find a name's definition and its class with
  `lookup`, a walk along a list of pairs.
- Dominance, the classes and the data are under a second together.

The validator is the model's, and nine proof files of the program
logic read `single_definitions`, so the repair is not this
campaign's to make alone. Decision 6 below is about it.

*The first repair.* `theories/core/ValidFast.v` counts every definition
in one pass into a map, and its `valid_fast` is `valid` with the
single definitions taken from that count. `valid_fast_eq` proves
`valid_fast md = valid md` for every module, so `valid` stays the
definition the proofs and the gates read, and the compiler runs
`valid_fast`. On SQLite, pizlonation and validation went from 24.8 s
to 17.2 s and the whole compile from 41 s to 33 s, with the same
text printed. The two `lookup`s are next; the blocks' own rules are
4.0 s of what is left and the reuse forms' stage about 5.

*Numbered temporaries gain nothing.* A pass that numbered a
function's temporaries and gave the plans integer names was written
and measured: the validator and the plans took the same time. What
they pay for is the walk along a list, not the comparison of two
names at each step. So the repair is maps in place of the lists,
with whatever names, and the pass is not in the tree.

*pcre2 through `rxc`.* With `NANOFIL_BACKEND` set, `rxc` and the
experiment's `run.sh` compile the IR with `nanofil-backend compile`,
and no Prolog runs after the regex compiler. The experiment's checks
pass: the module of 36 functions is Prolog's plain compile byte for
byte, `bench` agrees with PCRE2 on every pattern, and `hook`
compiles its 39 patterns and agrees on all of them.

Compile time, on an orb:

- The module of 36: 0.39 s, against 1.4 s for `nanofil compile` and
  6.3 s for `nanofil -O compile`.
- A cold cache of 39 patterns through the hook: 4.5 to 4.7 s,
  against 12.8 s. That is 120 ms a miss against 330.
- One pattern, for a small, a middling and a large one: the regex
  compiler 44 to 58 ms, the backend 16 to 43 ms, `as` 7 to 12 ms and
  `ld` 17 to 19 ms. `nanofil -O compile` takes 214 to 548 ms for the
  same three.
- The large one's 43 ms are 2 reading, 24 pizlonating and
  validating, 10 lowering and emitting, 1 printing, and 6 outside
  those.

So the 10 ms target is missed by two to four times, and validation
is again the largest part. A miss is now bounded as the target
wanted, by the regex compiler in SWI-Prolog and three process
starts, at about a tenth of a second.

*With M5b's passes.* `rxc` and `run.sh` now run `nanofil-backend
compile-promoted`. For the module of 36 it prints 45,702 lines,
`nanofil compile-promoted`'s byte for byte, in 0.35 s, against 1.4 s
for that command and 6.2 s for `nanofil -O compile`; the first
version's text is 99,256 lines, and `-O`'s 28,580. Per call, on the
nine benchmark patterns and as a multiple of `-O`'s time, the code
takes 2.10 in the geometric mean (1.56 to 2.91), where the first
version's takes 6.0 (2.8 to 16): the figure the Prolog selection
measured below. That is 3.0 to 11.8 times faster than PCRE2's
interpreter. A cold cache of 39 patterns through the hook takes
4.1 s, 106 ms a miss, against 4.5 to 4.7 s with the first
version.
`bench` and `hook` agree with PCRE2 on every pattern.

*The code's speed, and which passes it needs.* `nanofil compile` on
the module with one selection of `-O`'s parts at a time, then
`bench`. The figure is the geometric mean over the nine benchmark
patterns of the time per call, as a multiple of full `-O`'s:

- the first version's code: 6.2 (2.7 to 16);
- with selected branches: 5.5;
- with registers and selected branches, and no middle end: 4.0;
- promotion and copy propagation: 2.7;
- those and simplification: 2.6;
- those and inlining: 2.5, with the same count of assembly lines;
- promotion, copy propagation and selected branches: 2.1 (1.5 to
  2.9);
- all of `-O` but with stack homes: 2.2 (1.6 to 2.9);
- promotion, copy propagation, simplification and registers: 1.6;
- those and selected branches: 1.03;
- those and the combined checks: 1.08, and the inline `memcpy` 1.00;
- all of `-O` without simplification: 0.97.

Four things follow:

- Promotion with copy propagation is worth 2.3 times, registers
  1.7 to 2 times after it, and branch selection 1.1 to 1.6 times,
  the more the less other work is left.
- Promotion, copy propagation and branch selection are everything
  `-O` gives with stack homes. Simplification, inlining, the check
  passes and the inline `memcpy` do nothing for regex code.
- The experiment's README had stack homes at 1.1 to 1.7 times
  registers. Measured again it is 1.6 to 2.9, so the target of code
  within 2 times of `-O`'s waits for M7's allocator on most
  patterns.
- In Prolog the registers are also what compiling costs: the module
  takes 1.5 s with stack homes and 6.6 s with registers.

**The C++ build, measured at M6.** The target was within 2× of the
OCaml build, and it is missed: Crane's C++ takes 5 to 7.5 times the
OCaml build's time and up to 4 times its memory, and it is slower
than Prolog. Wall time and peak memory on an orb, IR text to
assembly, for the regex module `rx.ir` (36 functions) and for Lua's
`lvm.c` as IR; each build prints the same bytes:

- `compile`, `rx.ir`: Prolog 1.27 s and 43 MB, OCaml 0.34 s and
  57 MB, C++ 2.40 s and 76 MB.
- `compile`, `lvm.ir`: Prolog 2.87 s and 162 MB, OCaml 1.76 s and
  153 MB, C++ 8.36 s and 577 MB.
- `compile-allocated`, `rx.ir`: OCaml 0.39 s and 58 MB, C++ 2.87 s
  and 76 MB.
- `compile-allocated`, `lvm.ir`: OCaml 1.67 s and 153 MB, C++
  9.53 s and 501 MB.
- `compile-promoted` on one function of 19 kB of IR: OCaml 37 ms,
  C++ 164 ms. An empty module takes 3 ms in both, so none of it is
  start-up.

Where the time goes, by `perf record` on the C++ build:

- About 15% is freeing. A `Term` is a reference-counted tree, and
  dropping the last reference walks it. With `~Term` emptied by
  hand, as an experiment, the two `compile` runs took 2.05 s and
  7.22 s. The build keeps the destructor: without it nothing is
  freed, and the target is missed either way.
- With the destructor out of the profile, about 15% is copying and
  moving `Term` variants and 7% is `memmove`, and some parameters
  still go by value.
- The rest has no single hot spot.

`Set Crane Arena` was tried and is worse: slower, and ten times the
memory. So no switch closes the gap, and what would is more patches
to what Crane emits for values, matches and calls. That work is
proposed for M8, where the same C++ is built by filcc and its speed
first matters to a user; until then the OCaml build is the fast
one.

**The C++ build after M8's attempt.** M8 began with a bounded
attempt on Crane's output, with 2× the OCaml build on `rx.ir` as
the mark and 3× as the point to stop (decision 7). It stopped at
about 3×, and Crane's C++ is not taken further. Best of three on
an orb, `compile` and then `compile-allocated`; every build prints
the same bytes:

- OCaml: `rx.ir` 0.34 and 0.41 s at 56 MB; `lvm.ir` 1.72 and
  1.68 s at 149 MB.
- C++ as it is checked, with counted references: `rx.ir` 0.96 and
  1.30 s at 55 MB, which is 2.8 and 3.1 times; `lvm.ir` 4.75 and
  4.59 s at 382 and 371 MB, which is 2.8 and 2.7 times.
- C++ under `Set Crane GC`, with Boehm's collector as it comes:
  `rx.ir` 1.01 and 1.50 s at 79 MB; `lvm.ir` 5.07 and 4.82 s at
  410 and 436 MB.
- The same with `GC_FREE_SPACE_DIVISOR=1`: `rx.ir` 0.84 and
  1.13 s at 130 MB; `lvm.ir` 4.44 s at 548 MB for `compile`.
- The same with a first heap of 256 MB: `rx.ir` 0.76 and 1.01 s
  at 285 MB.

What moved it from M6's 2.40 s on `rx.ir`:

- Three switches took it to 1.17 s. `FastVariant` holds an
  inductive's alternatives in Crane's own variant, `BoxedFields`
  makes a field that is another inductive a pointer, as OCaml
  does, and `BoundedNesting`, which is ours, lets a term's
  destructor recurse once a level where it drained every list it
  owned into fresh cells.
- A change to Loopify took it to 0.96 s. `existsb`, `forallb` and
  a fixpoint of the shape `a || f rest` were loops over a stack of
  frames that copied every element; they are loops that stop
  early, with no frames. 81 functions keep a frame stack, where
  90 did.

`Set Crane GC` was the last experiment: no counts and no
destructors, a handle is a bare pointer, and every block comes
from a collector with Boehm's API. What it showed:

- All 52 inductives become trivially copyable and trivially
  destructible, as hoped. A `Term` is still 24 bytes, so it is
  not expected to travel in registers; that was not checked in
  the assembly.
- clang turns no more of the recursive functions into loops than
  it does with counts. Of the 12 Loopify declines, five keep a
  call to themselves in both builds, one has none in either, and
  six are inlined away.
- Memory was not flat until `crane::variant` was changed. A
  conservative collector reads the stale bytes of a variant's
  storage and padding as pointers, and the reachable heap climbed
  to 174 MB on `rx.ir`. With the storage cleared and the padding
  gone it stays near 30 MB through all 38 pieces.
- The collector is then the cost, and not the code. `compile` on
  `rx.ir` makes 17.65 million allocations, 14 million of them of
  32 bytes or less. With Boehm as it comes, `libgc` is 65 to 70%
  of the time, and the program's own code about 0.3 s, which is
  the OCaml build's whole run. With a large first heap it
  collects four times and `libgc` is still 48%, now in
  allocation. OCaml's allocator bumps a pointer and its collector
  is generational; Boehm's does neither.

So neither way of holding the data reaches 2×. Counted, the time
is in copies and destruction; collected, it is in the collector.
What is left is to allocate less, by more changes to what Crane
writes or to the Gallina, and that was not tried.

The collected build was also the first given to filcc, against
the Fil-C `boehmgc`, which is FUGC behind Boehm's API. It did not
finish. After 17 minutes of processor time and 8.9 GB the
compiler was in the Fil-C pass, in `computeFrameIndexMap`, which
finds the frame slots of a function's pointers, with 98% of the
samples there; at `-O1` it was in the same pass at the same size
when it was stopped after three minutes. So nothing is known of
FUGC's speed on this program, and a pizlonated library of Crane's
output would need that pass looked at first. The build was
stopped and that was not followed up.

**The CertiRocq C build (`rocq/backend/certirocq`).** CertiRocq
(`nix/certirocq.nix`, commit `943b52ae` patched against Rocq 9.1.1
and `MetaRocq` `1.5.1-9.1`) compiles the same six entry points
(`read_text`, `compile`, `compile_promoted`, `compile_allocated`,
`rev_lines_parts` and `first_todo`) with zero changes to the
backend's `.v` files. Its default `-O 1` pipeline (`--anf-variant 0`)
stalls in `inline_shrink_loop` past 200 s before and after closure
conversion. With `--anf-variant 8` (which skips `inline_shrink_loop`
while keeping `Shrink`, `Uncurry`, `Inline uncurry wrappers`,
`Lambda lift`, `Closure conversion and hoisting`, `Dead param elim`
and `Merge duplicate functions`), `CertiRocq Compile -O 1
--anf-variant 8` finishes in 157 s (`65 s` at `-O 0`) and emits
3,892,446 lines of Clight C (135 MB, 23,970 functions).

Best of three on an orb, `compile`, `compile-promoted` and
`compile-allocated`; every build prints the same bytes on the 52
IR fixtures, the 40 corpus `.ir` files, `rx.ir` and `lvm.ir`:

- Raw CertiRocq C (16 shards, `gcc -O1`, 19.3 s compile, needing
  `ulimit -s unlimited`): `rx.ir` 8.89, 12.28 and 13.77 s at
  185, 137 and 137 MB; `lvm.ir` 48.95, 48.89 and 91.42 s at 819,
  771 and 1,065 MB.
- With static string-literal folding (`split_nb.py`: 28,793 `Ascii`
  and 28,791 `String` runtime allocations folded into 3,425 static
  nodes, removing ~850k lines of C; `gcc -O1 -j16` builds in 9.8 s)
  and C overrides (`overrides.c`) for hot stdlib, map and reader
  loops: `rx.ir` **1.06, 1.12 and 1.32 s** at 101, 91 and 90 MB
  (3.1 to 3.2 times the OCaml build's 0.34 / 0.41 s mark, matching
  Crane's 0.96 / 1.30 s, with the default 8 MB stack); `lvm.ir`
  **8.07, 6.19 and 6.66 s** at 648, 641 and 640 MB.
- Built with `filcc` (`-DVERIFFI -O1 -j16`): sharded into 16 files,
  CertiRocq's C has no `computeFrameIndexMap` blowup (`mem2reg`
  promotes its destructor-free `register value` locals to SSA
  registers, leaving only `value root[K]` on the frame). Default
  `typedef intnat value` compiles in 54.1 s (1.15 GB RSS) and traps
  immediately at run time (`cannot read pointer with null object`)
  because casting pointers through `intnat` strips capabilities.
  With `-DVERIFFI` (`typedef void * value`, plus `(intnat)` casts on
  the three emitted tag-switch patterns), `filcc` builds in 143 s
  (1.96 GB max RSS) and runs cleanly without changing `gc_stack.c`:
  on `rx.ir`, the raw build takes 165.4 s at 994 MB (`compile`), and
  the folded + overridden build takes **9.54, 8.39 and 10.40 s** at
  512, 424 and 433 MB (a 17.3× speedup over raw `-DVERIFFI`, and
  7.5 to 8.5× native folded CertiRocq C because every `value` word
  carries a 16-byte Fil-C capability in `void *` slots).

Why CertiRocq's C stops at ~3.1× natively and ~7.5–8.5× under
`filcc`:

- Without primitive mappings, every character of every string
  literal in `nb.c` allocates a 9-word `Ascii` block and a 3-word
  `String` cell at run time, `nat` is unary Peano `O | S n`, and
  `Maps.string_hash` runs 20-bit binary long division per character
  (84,488 minor/major GC calls and 44.3 GB of nursery traffic on
  `rx.ir` `compile` before folding and `overrides.c`).
- Top-level non-function `Definition`s become `let` bindings in
  `body()` rather than globals in `gfuns`, so functions that
  reference more than `--c-args 5` constants/parameters or a
  constant across more than `max_push = 1` call (`IrText.read_step`
  with 31 character constants, `Maps.hash_step`, `ZMap.Raw.create`,
  `ZMap.Raw.bal`) fail to lambda-lift (7,675 of 23,970 functions),
  and `inline_uncurry` runs one pass so 3+-argument functions
  allocate intermediate curried closures.
- Every function with a non-tail call or GC check links a local
  `struct stack_frame frame` into `tinfo->fp = &frame`, which
  prevents the C compiler from tail-call-optimizing recursive loops.

**Crane's `joom/refactor` branch.** One more bounded round, on the
advice of Crane's author: his `joom/refactor` branch at `fa70df57`,
the settings of its `libraries/parse-a-lot-bench/CraneExtraction.v`,
and separate extraction with no clang-format. It reaches the 2×
mark natively, and its C++ builds and runs under Fil-C, slowly. It
is an experiment that no check builds: the checked C++ build is
still the one on the old pin.
[`rocq/backend/crane/joom-refactor`](https://github.com/mbrock/filnix/tree/a8083f593eeb47a6e1e919a84f53bbe718e8594f/nanofil/rocq/backend/crane/joom-refactor), removed from the tree
in November 2026, had the patch to Crane, the changes to the
backend's Crane files, and `build.sh`, which extracts, repairs,
compiles and links.

The settings are `Loopify`, `NonAtomicRc` and `SharedVariant`,
`Format Style "None"` and `Crane Separate Extraction`. A shared
variant is one word: a tag for an alternative with no fields, or
the address of a counted block that holds the alternative. Copying
one is a count bump, where the old pin's variant copied its
storage. As it comes it is written in C++26, so the native
compiler is clang 21 at `-std=c++2c`.

Best of three on an orb, `compile` and then `compile-allocated`.
Every build prints the OCaml build's bytes on `rx.ir` and `lvm.ir`
and passes `crane/tests/same.sh` on the 26 fixtures for `compile`,
`compile-promoted` and `compile-allocated`: 17 the same, 6 refused
alike, 3 not taken by either.

- OCaml: `rx.ir` 0.36 and 0.46 s at 56 MB; `lvm.ir` 1.92 and
  1.85 s at 149 MB.
- C++ as it is checked (M8): `rx.ir` 0.96 and 1.30 s at 55 MB;
  `lvm.ir` 4.75 and 4.59 s at 380 MB.
- The branch, native: `rx.ir` 0.70 and 0.89 s at 41 MB; `lvm.ir`
  3.56 and 3.28 s at 297 and 283 MB.
- The branch, under Fil-C: `rx.ir` 9.66 and 12.78 s at 228 MB;
  `lvm.ir` 51.0 and 45.9 s at 1.2 and 1.1 GB.

So the native build takes 1.9 times the OCaml build's time on
`rx.ir` and 1.8 to 1.9 on `lvm.ir`, where the checked one takes
about 2.5 to 2.8, and less memory than the checked one. The OCaml
figures are this round's run. In others it took 0.34 and 0.41 s,
and 1.72 and 1.68 s; against those the native build is at 2.1 to
2.2 on `rx.ir` and 1.9 to 2.1 on `lvm.ir`.

What each setting is worth, natively, on `compile`:

- Without `SharedVariant`, on `std::variant`: 2.30 s on `rx.ir` and
  7.60 s on `lvm.ir`. A third of that profile is the variant's own
  machinery.
- Without `Loopify`: 0.66 s at 99 MB on `rx.ir`, and 5.38 s at
  520 MB on `lvm.ir`, and it needs an unlimited stack.
- With `list` mapped to `crane::list` as well, which the benchmark
  file also does: 1.07 s at 30 MB on `rx.ir` and 5.75 s at 185 MB
  on `lvm.ir`. Slower, with the least memory. The build measured
  above leaves it out.

Building is faster too. Extraction takes 13 to 15 s, where the old
pin takes about two minutes. The 50 files compile in 50 s on 16
cores, 6 minutes of processor time, the longest in 38 s.

*What the branch still needs from us.* The patch has eight parts
for the native build:

- the port to Rocq 9.1;
- a custom match's scrutinee instantiated, as on the old pin;
- numerals folded at any size: without it `two64` is 0;
- a string literal written as one `std::string("...", n)`, which
  also halves the C++ compile time;
- Loopify's default branch kept, in three files: without it
  `merge_steps` dropped the prefix it had built, and ten fixtures
  differed;
- an eta-expanded function's arguments computed once: without it
  `proof_pointers` was found again for every block, and `lvm.ir`
  took over a minute;
- `#include <atomic>` in `shared_variant.h`;
- a type alias of a shared variant held as a shared box
  (`Text.parts`): without it 25 errors of pointer type.

One part of the old patch is fixed upstream (the free variables of
a switch's default). Five were not carried over, and the gate
passes without them: the order of assignment in `rc.h`, borrowing
in eta expansions, early exit from loops, `BoundedNesting` and
the collected mode.

The output needs three repairs before it compiles, which
`build.sh` makes with `sed`: a call that two namespaces make
ambiguous, a receiver type written without its namespace, and a
global built from a variable template that may be initialized
after it is read. The last is a real fault and not a matter of
style: under `SharedVariant` the global copied a null box, and 15
fixtures threw. The link needs `-z muldefs`, since Crane defines
functions in headers that are not inline.

*Under Fil-C.* Fil-C's compiler is clang 20.1.8. Two more parts of
the patch are for it, and the native build is the same bytes with
them:

- `shared_variant.h` binds an alternative's fields as a pack,
  which clang 20 does not have. It counts the fields and binds
  that many names where packs are missing.
- A shared variant kept its block's address as an integer, which
  carries no capability: the program stopped in a global
  constructor with "cannot read pointer with null object". The
  word is a pointer now, and a slot is swapped a word at a time.

With those the Fil-C build passes the same gate on all three
commands. Separate extraction is what makes it compile at all: the
monolithic file of M8 was stopped after 17 minutes and 8.9 GB in
`computeFrameIndexMap`. The 50 files take 8 minutes on 8 cores
and 38 minutes of processor time between them; the longest takes
five and a half minutes, and the largest 2.0 GB. No native file
takes 40 s, so the compiler is still slow on this code, and the
time follows the pointers: with the word an integer the same
files took 18 minutes of processor time, for a program that then
does not run. Where the compiler spends it was not profiled this
round.

It runs 14 times slower than the same C++ built natively, and 27
times slower than the OCaml build, where Fil-C's usual cost is 1.5
to 4 times:

- By `perf` on `rx.ir`, 78% of the samples are in the runtime and
  63% in FUGC's marking. The marking is on other cores: the run
  takes 31 s of processor time in 10 s.
- A larger heap before the first collection
  (`FUGC_MIN_THRESHOLD` at 256 MB) cuts the processor time to
  12 s and the run only to 9.5 s. So nearly all of the run is the
  program's own thread, where the native build takes 0.7 s.
- With a first heap of 1 GB the runtime is still a third of the
  samples, and its largest part, a tenth of all of them, is
  `filc_object_ensure_aux_ptr_outline`. By its name that gives a
  block the storage for its pointers' capabilities, and this
  program makes millions of small blocks that hold pointers;
  that reading was not checked in the runtime's source.
- The `std::variant` build of the same branch is slower still
  under Fil-C: 26.1 and 34.0 s on `rx.ir`.

CertiRocq's C under filcc takes 9.54 and 10.40 s on the same
input, so the two are about level there, and neither is near the
4× target for pizlonated code. A process start of the OCaml build
is still the fastest way to compile a pattern.

## Milestones

Each ends with its gate green and a short note of what it found.

**M0. The plan and the project.** This document. `rocq/backend/`
with its `_RocqProject`, a build script, extraction to a
`nanofil-backend` binary and a Nix check outside the quick gate.
Gate: the empty project builds, extracts and passes `parse.sh`.

*Done.* `make -C rocq/backend` builds `nanofil-backend` in two
seconds. It compiles only the model files the backend imports, which
is `Term.v` so far, so it does not wait for the model's proofs. The
flake checks are `nanofil-backend`, which takes ten seconds once its
inputs are built, and `nanofil-backend-full`. They have their own
workflow, and the quick Rocq gate does not read the directory.

**M1. Asm lines and the printer.** `Asm.v`: lines, directives,
operands and expressions as inductives, a decoder from terms, and
the printer. A Prolog command prints a module's line list as terms.
Gate: for the corpus, the printed text equals `nanofil compile`'s,
byte for byte; the per-stage baseline is measured and recorded here.

*Done.* The command is `nanofil asm-terms FILE TEXT`, which writes
the text and prints the lines it is the text of. `Asm.v` has the
types and the printer, `AsmTerm.v` the decoder, and
`rocq/backend/tests/asm.sh` is the gate. The text is the same for
all 280 Fil-C modules of `tests/filc`, `tests/c` and `tests/c/prog`,
with and without `-O`, and for SQLite's 5.52 million lines. Seven
files are skipped: six that nanofil refuses without their test's
flags, and one plain module. Found:

- A `match` on string literals extracts to a decision tree per bit:
  the decoder was 11,701 lines of OCaml. Names are compared with
  `String.eqb` instead, and it is 1,713.
- A driver that holds a module's terms, lines and parts needs 4 GB
  for SQLite. It now works a chunk of lines at a time.
- The baseline is under Performance targets above.

**M2. Frames and the ABI plan.** `filc_abi.pl` and `frame_slots.pl`:
slots, roots, entry and exit actions, call layouts, signatures.
Gate: the plan of every corpus function in the subset equals
Prolog's, as terms.

*Done.* The command is `nanofil abi-terms FILE`, which prints the
checked module, the plan of each function and the plans of its weak
thunks. `Plan.v` has the plan's types, whose instructions are
`Syntax.v`'s. `Fuse.v` joins a check to its access, `Liveness.v`
and `FrameSlots.v` give temporaries their slots, `Abi.v` builds the
plan, and `Order.v` is Prolog's standard order of terms, which the
plans are sorted by. `IrTerm.v` and `PlanTerm.v` write a plan as
Prolog's term, and `rocq/backend/tests/abi.sh` is the gate. Only the
reference path is compared, without `-O`.

On the 280 modules of the corpus, the plans of 1089 functions and
all 280 lists of thunks are the same terms. The backend refuses no
function of the subset. The model keeps 576 functions outside it,
and they are passed over: 535 for `touch`, 12 for `asm_fixed`, 11
for `fence`, 9 for `setjmp` and 9 for `raw_cas`. On SQLite all 3106
plans and the thunks are the same, with nothing outside. Found:

- `filc_abi.pl`'s `adapter_return/2` zeroed too few aux words when a
  tuple with a float came back. Its test for a float left `K` bound
  to the first float's class, and the list of zeros then kept only
  the cells of that class. For `tuple([l, s])` the adapter zeroed
  `aux(1)` and left `aux(0)` as it was, which let a caller reading
  the result as a pointer use a stale capability. Prolog is fixed
  (21ca173), and `Abi.v`, which had followed it to give the same
  plan, now zeroes the aux of every cell that holds no pointer.
- `touch` is the pizlonated `access`, and it keeps a third of the
  corpus's functions out of the gate. It is the first construct to
  ask the model's owner for.
- Building SQLite's plans took 7.8 s in OCaml, more than the whole
  M3 target of 2.7 s. The profile under Performance targets brought
  it to 2.6 s and says where the rest goes.

**M3. Stack-homed emission.** `filc_amd64.pl`'s reference emission
and `amd64.pl`'s scalar selection, in pieces: scalars, compares and
jumps first; then checks, flights, raw accesses and polls; then
calls, variadics, function objects, data, aliases and TLS. Gate:
whole-module byte identity on the corpus, hello, zlib and Lua, with
the first performance target.

*So far: every list of every module, and whole modules.* The
command is `nanofil emit-terms FILE`, which prints the checked
module and then the reference emission's lines as terms: a list for
each item, for each weak thunk and for the end of the file.
`Layout.v` has a function's context and the loads and stores of
homes. `EmitOps.v` is `amd64.pl`'s scalar selection, with SSE2 and
x87. `EmitInst.v` emits one instruction of a plan: lets, span tests,
flights, fused and reused accesses, pointer effects, named locals,
calls and the ABI's actions. `EmitObject.v` emits a function's
getter, generic entry, variadic adapter and object, and `Emit.v` the
function. `EmitData.v` emits a data object with its relocation
table, a thread-local object, an init entry, a weak declaration and
an alias's getter. `EmitThunk.v` emits a weak thunk, and
`EmitModule.v` puts the lists in the file's order.

`rocq/backend/tests/emit.sh` is the gate. It emits each list again
from the module and compares it, as text, with the reference's.
Then, without `-O`, it compares what `nanofil-backend module` prints
for the module with what `nanofil compile` prints for the file. For
a preprocessed `.i` file the text is `nanofil cc`'s, which is what
`nanofil-cc` runs on a package's translation units.
Emission is total: a form that is not ported gives a `todo` line,
and the gate counts such a list as partial. None is left. The todos
that remain in the code stand where Prolog itself fails or throws.

- On the 280 modules of the corpus, all 1090 functions of the
  subset, all 2394 lists of data and aliases and all 1630 weak
  thunks are the same. The 576 functions outside the subset have no
  plan and are passed over. The 237 modules with no such function
  are `nanofil compile`'s text byte for byte, and the other 43 have
  no whole text yet.
- On SQLite all 3106 functions, 1843 data lists and 181 thunks are
  the same, and the whole module is `nanofil compile`'s 135 MB of
  assembly byte for byte.
- zlib, GNU hello and Lua are built through `nanofil-cc` with each
  preprocessed translation unit kept, and each unit's text is
  compared. All 17 units of zlib and all 81 of hello are
  `nanofil cc`'s text byte for byte, and 33 of Lua's 34. The one
  left is `ldo.c`, whose `luaD_rawrunprotected` calls `setjmp`;
  its other lists are the same. The three have 1,481 functions
  of the subset, 1,327 data lists and 1,385 thunks between them.
  The full check builds and compares them; it takes six minutes
  on 16 cores.
- In OCaml, SQLite's plans take 2.8 s and its functions' emission
  1.5 s. `nanofil-backend module` lowers and emits the whole of it
  in 3.9 s and prints it in 1.75 s, within 1.7 GB, where Prolog's
  emission stage takes 20.6 s. The target for lowering and emission
  is 1.0 s, so they miss it by four times; the profiles under
  Performance targets say where the time goes.
- `EmitModule.v` gives the module as pieces: one per item, one for
  the weak thunks and one for the end of the file. The driver asks
  for a piece, prints it and drops it, so a module's lines are
  never all alive. Before that SQLite took 6.0 s to lower and emit
  and 2.3 s to print, most of the difference in the collector.
- With `-O` the lines of 538 corpus functions are the same, with
  all the data and thunks, and the backend refuses 256 when it
  builds their plans. Every one of the 256 has a reuse form
  (`renew`, `renew_hull`, `renew_if`, `half_check` or a limit
  check), which `Fuse.v` leaves to M9, so they are not M3's.
- `rocq/backend/tests/edge` has two fixtures for the arms the
  corpus does not reach. `calls.ir` has calls whose arguments end
  at cells 16, 17, 32 and 33, a pointer cell at exactly cell 32,
  results in a buffer and float tuples. `data.ir` has a weak
  read-only object, a negative addend, alignments of 64 and 128,
  thread-local objects with pointers, and every kind of init entry
  and alias. A mutation of the pointer cell limit in a thunk
  survived the corpus and is caught by `calls.ir`.

What it showed:

- Porting a predicate at each of its call sites hides a wrong
  port. `result_registers/4` gives a tuple's third float word an
  integer register once `%xmm0` and `%xmm1` are taken. Three
  function-side ports of it gave that word nothing, and the corpus
  has no such call. The thunk port followed the clause order, and
  a fixture then showed the difference. It is now one definition
  in `Layout.v`, shared by the function, the call, the generic
  entry and the thunk.
- Some arms cannot be reached through the gate, because the
  validator rejects their input: an alias with `local` linkage, an
  alias of a weak declaration, and a negative `x` constant. An
  alias of a thread-local object was among them until Prolog began
  to take one; `tests/edge/data.ir` now has one of each linkage,
  since C cannot write the local one.
- A data object of 200,000 items overflows the 8 MB stack in the
  driver, with the stub emission as with the real one. With an
  unlimited stack the lines are Prolog's. `payload_items` is not
  tail-recursive either, so M5 looks at both.

What remains of M3:

- the functions outside the subset, which wait on the model: `touch`
  first, and `setjmp` for Lua's `ldo.c`. With them come the 43
  modules of the corpus that have no whole text. `touch` has since
  come: the model has `Touch`, the backend fuses it with its check
  as `filc_amd64.pl` does and emits the check alone, and 26 more
  files of the C corpus print Prolog's text;
- the performance target. The profile says it is not met by the
  emission alone: it needs M5's numbered temporaries and a faster
  reader.

**M4. Pizlonation and a standalone compiler.** `Pizlonate.v` and a
Gallina reader for IR text. The pipeline is read, pizlonate,
`valid`, lower, emit, print. Gate: the pizlonated module equals
Prolog's as a term, and `nanofil-backend compile FILE.ir` equals
`nanofil compile FILE.ir` with no Prolog in the pipeline. Done.

*Pizlonation is done.* `Pizlonate.v`'s `pizlonate_module` takes a
module's term and gives the term pizlonate.pl gives: every access
with its check, the flight forms, a poll on each edge to a block at
or before its source, the `loc` markers of an unchecked module
dropped, and the context items dropped. It gives nothing where
Prolog fails or throws.

- **No `Unchecked.v`.** The plan was an inductive for the unchecked
  instructions. Pizlonation does not need one: it looks at a few
  instruction shapes and passes every other term through, so on
  terms it is 700 lines, and `Transport.decode_module` then reads
  its result into `Syntax.v`'s types, keeping a function outside the
  subset as `IOutside`. An inductive would have been a second copy
  of the instruction grammar, with a decoder and a printer to keep
  in step.
- **The gate** is `tests/pizlonate.sh`: `nanofil pizlonate-terms`
  prints a module and then pizlonate.pl's result, and the backend
  must make the second from the first. The corpus, with and without
  `-O`, the package translation units and SQLite are 857 modules and
  18,191 items, all the same. SQLite's 4,949 items take 0.9 s, after
  1.7 s to read the term.
- **Mutations.** 36 wrong ports were tried, and an `Example` or the
  gate catches 35. Nine of those got past the corpus alone, and
  each showed something the corpus does not have: a module that is
  in filc mode for one reason only (an external call, a weak
  function, read-only data, an alias, a local object), a checked
  module with a `loc` marker, and a name `chk0` taken by a phi or a
  parameter. Those are now the fixtures of `tests/pizlonate/`.
  The one left, keeping the context items, cannot show in this
  gate, which prints modules without them; the standalone
  compiler's gate reads them.

*The standalone compiler is done.* `nanofil-backend compile
FILE.ir` reads the text with `IrText.v` and compiles the module
with `Compile.v`: pizlonate, read into `Syntax.v`'s types, the
model's `valid`, lower, emit, print. It exits 1 for a module it
refuses and 3 for one it does not take: a plain module, whose
backend (amd64.pl) is not ported, or one with a function outside
the subset.

- **The reader** takes what ir_text.pl's printer writes and a
  little more: comments, names, quoted atoms and strings with their
  escapes, symbol atoms, decimal integers, compounds, proper lists,
  and one operator, the infix `-` of a phi's edges. It gives nothing
  for the rest of Prolog's syntax. The rule is that it never reads a
  text differently from SWI-Prolog; it may refuse what Prolog reads.
  Every loop is a tail call, so a module of 200,000 items needs no
  more stack than one item.
- **The reader's gate** is `tests/read.sh`, with a new command
  `nanofil read-each` that prints the module Prolog reads from each
  file. The fixtures and 387 texts of the corpus all read the same.
  Of 1,088 adversarial texts (escapes, quotes, UTF-8, numbers,
  operators, comments, clause ends), 626 read the same, both refuse
  227, and the reader alone refuses 235. `tests/read/refused.txt`
  names those 235, and the gate fails if the set changes either way.
  The largest groups are uses of `-` that are not a phi's edge,
  number forms other than decimal, and bytes outside ASCII that are
  not inside quotes.
- **A text in pieces.** The driver gives the reader the file a
  megabyte at a time, and a piece is a list of characters only while
  its clauses are read. For SQLite's 78 MB of text this is 1.3 GB at
  the peak in place of 2.8 GB, at the same speed. That reading in
  pieces equals reading the whole list is not proved: two `Example`s
  cut a text at every size from 1 to 40, and the gate runs the
  adversarial texts again in pieces of one byte and of seven.
- **The compiler's gate** is `tests/compile.sh`: the text printed
  must be `nanofil compile`'s, byte for byte, and each must refuse
  what the other refuses. The IR fixtures give 32 the same, 4 not
  taken and 7 refused by both. The C corpus and the package
  translation units give 374 the same and 24 not taken (17 with a
  function outside the subset, 7 plain); the frontend skips 7. The
  files not taken must be exactly the 28 that
  `tests/compile/none.txt` names, so the gate fails when the
  backend stops taking a file, and when it starts taking a listed
  one.
- **Three known gaps**, all on the side of taking less or checking
  less than Prolog, none of which changes a line both print:
  - A function's name must be an atom; a data object's may be any
    term, as in Prolog.
  - The `context/2` items are dropped unchecked. Prolog checks
    provenance's records before it drops them.
  - Prolog also runs `valid_module/1` on the module as written.
    Here only the pizlonated module is judged.
- **Mutations and fuzzing.** Of 25 wrong readers, the gates catch
  24; the last showed that a test in the symbol atoms was redundant,
  and it is removed. Of 6 wrong versions of `Compile.v`, an
  `Example` or the gate catches 4. The other two cannot show: one
  skips the early exit for a function outside the subset, which the
  driver then finds as a missing plan, and one asks an atom of every
  five-argument item, and only `func` has five. Of 5,876 mutated
  IR texts, 1,127 compile to the same bytes, both refuse 4,582, and
  167 that Prolog compiles are not taken, as plain or outside the
  subset. No text differs, and the backend compiles nothing that
  Prolog refuses.
- **SQLite.** `compile` on SQLite's IR text prints Prolog's
  assembly, byte for byte, in 41 s and 1.3 GB, against 70 s and
  2.1 GB for `nanofil compile`. Reading is 9.6 s, pizlonation and
  validation 24.8 s, lowering and emission 4.9 s, printing 2.0 s.
  Pizlonation is under a second of that, so the model's validator
  is more than half of the whole compile. It was written to be
  proved about, not to be fast, and it is M5's first target.

The driver's input stays text. An NFB reader is proved
(`Nfb.decode`), but its checked decoding of SQLite's two stages
took 17 s, where the text reader takes 9.6 s for the first and the
driver's OCaml reader of Prolog's terms about a second. It becomes
the input when it is the faster one. The NFB work now aims at
decoding straight into M5's numbered form: `Syntax.v`'s own types
with a temporary named by an integer term, symbols keeping their
names, and a function outside the subset kept as a term.

The full check (`nanofil-backend-full`, about an hour) runs only
when asked, by `workflow_dispatch`; the quick one runs on pushes
that touch the backend's paths or the seven Prolog files it must
match (`ir_text.pl`, `pizlonate.pl`, `promote.pl`, `copy.pl`,
`filc_abi.pl`, `filc_amd64.pl` and `asm.pl`), and on no others.

**M5. Speed, and pcre2 through `rxc`.** Profile, fix data
structures, record the numbers in perf.md's style. `rxc` gets a
switch that runs `nanofil-backend` in place of the Prolog compile.
Gate: the second performance target; the experiment's checks pass
with the extracted compiler; the miss time and the code's speed are
recorded, with a list of the `-O` passes that code needs.

*Measured, and half done.* The numbers are under
[Performance targets](#performance-targets).

- Done: the `rxc` switch, the experiment's checks with the extracted
  compiler, the miss time, the code's speed and the list of passes.
- Not done: the second performance target. After reading, SQLite
  takes 32 s, and the target is a fiftieth of Prolog's 53, about a
  second. The model's validator is 18 to 20 s of it and quadratic,
  and its repair needs the model's owner. Reading is 10 s more, and
  waits for the NFB reader. The plans and the emission still find
  names in lists.
- Dropped: numbering the temporaries, which measured as no gain.

**M5b. The middle end pcre2's code needs.** Promotion and what it
stands on: the CFG and dominators of `cfg.pl`, `escape.pl`,
`promote.pl` and `copy.pl`, about 2,100 lines of Prolog. They run
before pizlonation, on the unchecked module, and their result is in
the first version's forms, so nothing after them changes. With them
comes the selection of branches in the emission (`compare_branch`
and `selected_jump` in filc_amd64.pl, under 100 lines): a branch
reads the flags of the comparison before it, and an edge to the
next block falls through. `simplify.pl`, inlining and local storage
are left out: M5's list says regex code does not need the first
two, and local storage changes nothing in the regex module. Gate:
byte identity on the corpus with the Prolog compiler run with those
parts alone (opt.pl's `passes([promote, copy])`, which leaves local
storage off, with `--registers=stack --branches=selected
--memcpy=call --checks=reference`), and the regex experiment's
patterns at the 2.1 times of full `-O` that this selection measures
in Prolog. This is the first point where the `rxc` route is worth
switching on.

- Reached: copy propagation. `Copy.v` makes of a promoted module
  the term `copy.pl` makes of it, on `TermCfg.v`'s blocks, CFG and
  strict-SSA check, which reuse the model's `Cfg.v` dominators.
  `tests/promote.sh` holds it to `nanofil promote-terms`, which
  prints the module, its promotion and the copy pass's result: the
  same on every file of the corpus nanofil accepts, where copy.pl
  changes 1,034 functions in 221 files.
- Reached: escape analysis and promotion. `Escape.v` finds the
  allocs whose address does not escape and their accesses, and
  `Promote.v` makes of a module the term `promote.pl` makes of it:
  the slots of an alloc as temporaries, with pruned phis, punned
  reads as shifts, `l` accesses split into words, and float slots
  only where a store comes before every load. The same gate holds
  it to the second term `nanofil promote-terms` prints: the same on
  every file of the corpus nanofil accepts, where promote.pl
  changes 1,384 functions in 261 files, and on all 4,949 items of
  SQLite, which it promotes in 2.8 s. The fixtures of
  `tests/promote` reach each arm in the quick check; 13 mutants of
  `Promote.v` each make one of them differ.
- Reached: the selection of branches. `Emit.v`'s `function_code
  true` gives a branch the flags of the comparison before it, where
  that comparison's result has no other use, and lets an edge to the
  next block fall through, as `compare_branch` and `selected_jump`
  do. 40 mutants of it each make a file of the quick check differ,
  and the fixture `tests/promote/selected.ir` reaches each of its
  cases.
- Reached: the byte gate. `nanofil-backend compile-promoted` runs
  promotion, copy propagation and the selected emission, and
  `tests/compile.sh` with `COMMAND=compile-promoted` holds its text
  to that of the new `nanofil compile-promoted`, which is
  `passes([promote, copy])` and `emit(stack, selected, call)` with
  the reference checks. The same on 376 C programs and translation
  units (2,527,096 lines) and 38 IR fixtures; the files not taken
  are those of `compile/none.txt`, and none differs.
- Reached: the regex figure, 2.10 times full `-O` per call, and the
  `rxc` switch now runs this compiler. The numbers are under
  [Performance targets](#performance-targets).

**M6. Crane.** Build Crane in Nix against our Rocq, extract the same
entry points to C++, compile with clang++ and run the same
differential tests. Gate: byte identity again, and the C++ target.
If Crane cannot extract the development, the note says what stopped
it, and the order of remedies is: change the Gallina, use a Crane
switch, patch Crane, fall back to CertiRocq.

*Done, but for the speed target.* Crane at commit `c2aadd9`, with a
patch of ours, extracts the reader of IR text, `compile`,
`compile_promoted` and M7's `compile_allocated` to 36,106 lines of
C++23. clang builds them with a driver of 127 lines as
`nanofil-backend-cpp`, which prints what Prolog and the OCaml build
print, byte for byte. It takes 5 to 7.5 times the OCaml build's
time (about 3 after M8's attempt), so the 2× target is missed; the
figures and the profile are under
[Performance targets](#performance-targets). CertiRocq was
not needed.

- **The gates.** `tests/compile.sh` holds `compile` and
  `compile-promoted` to Prolog: the same bytes on 376 C programs
  and translation units and on 38 IR fixtures, with no file
  differing. That run was before M7's files joined the extraction;
  the check repeats it on the fixtures with them. Prolog has no
  `compile-allocated`, so `crane/tests/same.sh` holds that command
  to the OCaml build's exit status, output and message: the same on
  252 translation units of the corpus as IR and on 39 fixtures, the
  other 18 and 13 not taken or refused by both for the same reason,
  and no file differing.
- **The mappings.** `CraneMap.v` gives `positive`, `N` and `Z` to
  `nf::Z` of `nfrt.h`, a 64-bit word that becomes a GMP integer
  when a result does not fit; `nat` to `uint64_t`, `ascii` to `char`
  and `string` to `std::string`. `CraneSelfTest.v` holds every
  mapped function to what `vm_compute` finds for it, on numbers at
  and past 64 bits, and `selftest.cpp` runs that in the check.
- **The check.** `nanofil-backend-crane` in the flake
  (`nix/backend-crane.nix`) builds Crane (`nix/crane.nix`), extracts,
  compiles, and runs the self-test and the three gates on the IR
  fixtures and `tests/regs`, and reads the Crane files back with
  `parse.sh`. It needs no Fil-C toolchain. On 16 cores it takes nine
  minutes: two to extract, four for clang on the one translation
  unit, and two for `parse.sh`, which extracts once more. So it is a
  job of its own in the Nanofil Backend workflow and no part of the
  quick Rocq gate.

What stopped Crane, in the order of the remedies:

- *Changed in the Gallina.* Three names whose C++ did not compile
  (`fixed` and `text` renamed, `names` made a notation), two local
  functions made top-level, and `Order.v`'s four merges written as
  top-level fixpoints on a count of steps. Each merge was a
  fixpoint over one list holding a local one over the other, a
  shape Crane's loop transform declines, and the recursion
  overflowed the C++ stack in `Abi.frame_of`. Prolog's bytes still
  match after each change.
- *Switches.* `Loopify` turns recursion into loops, and
  `NonAtomicRc` makes the reference counts plain integers. M8
  added `FastVariant`, `BoxedFields` and `BoundedNesting`.
  `NoLoopify` is set for `term_eqb` and `Order.term_compare`, for
  which Loopify's C++ names a function it never declares. Loopify
  still declines 12 functions, which stay recursive: the stdlib
  AVL map's `join`, `map2`, `combine` and `equal`, the validator's
  three walks along a chain of definitions (bounded by fuel), the
  two walks of a dominator tree, and `Abi.one_per_symbol` over a
  module's thunks. None has overflowed on the corpus. `Arena` was
  tried and rejected.
- *Patched in Crane* (`nix/crane-nanofil.patch`, 705 lines in 17
  files at M6, and 1,277 in 24 with M8's three additions at the
  end of this list):
  - the port to Rocq 9.1, which is API changes in six files;
  - a string literal is one `std::string` with its length and
    octal escapes, and a character literal is escaped the same way;
  - Loopify skipped a switch's default branch, so a `return` there
    dropped the list built so far;
  - numerals were folded in `int64` and wrapped silently from 2^63;
  - `rc.h`'s assignment released the old block before counting the
    new one, which frees `p->tail` in `p = p->tail`;
  - costly values are borrowed by `const &` where they were copied,
    a closure may be called more than once, and a match under a
    let's right-hand side is translated;
  - M8: the `BoundedNesting` switch, under which a type that
    recurs through another, as a term does through a list of
    terms, has no draining destructor;
  - M8: Loopify writes `existsb`, `forallb` and fixpoints of the
    shape `a || f rest` as loops that stop early;
  - M8: the `GC` switch, which is off. The header defines
    `CRANE_GC`, under which `rc.h`'s handle is a bare pointer,
    blocks come from `GC_MALLOC`, no destructor is written, and
    `crane::variant` keeps no stale bytes. `main.cpp` and
    `nfrt.h` follow the same macro, and the program links
    `libgc`. No check builds it: it was held to the OCaml build's
    bytes on `rx.ir` and `lvm.ir` by hand, when it was measured.

Three of those (the default branch, the numerals and the
assignment) made C++ that compiled and computed something else.
That is the argument for keeping the gates on every change to the
backend: Crane is an alpha, as its site says, and its output is
trusted only as far as it is compared. The patch is ours to
maintain; none of it has been offered upstream yet.

**M7. A fast simple register allocator.** Designed for a proof, not
ported. Gate: difftests and package checks by behaviour, and a
measured run-time gain over stack homes on the benchmark gate.

*Done.* `Regs.v` (`nanofil-backend compile-allocated`) numbers each
function's temporaries into `nat` identifiers, recognizes adjacent
single-use `flight` + `check` accesses and integer `let` + `cmp` +
`branch` sequences so ephemeral values stay in `%rax` without taking
a register home, builds closed sub-intervals per block from CFG
liveness, and colors integer (`w`, `l`) temporaries and pointer (`p`)
address words in descending `4^depth` natural-loop weight order over
`%r10`, `%r11`, `%rbx` and `%r12`–`%r15`, preferring a colored phi
partner's register first so loop induction updates coalesce in place.
Capability lowers stay in their `lowers[]` frame roots, and any
temporary live across a call, helper call (`AStorePointer`,
`ADispatch`, `alloc`, getters, `va_arg`) or `poll` edge takes only
callee-saved `%rbx` or `%r12`–`%r15`, saved after the stack check and
restored before every `leave`. Phi edges compile via a parallel-move
scheduler using `%rax` and cycle-breaker `%rcx` with no shadow slots,
and scalar operations select directly into assigned registers with
three-address `lea`, `imm32` operands and narrow loads and stores.

- **Validation and proofs.** Every allocated function is checked
  before emission by a linear-time Gallina validator (`valid_alloc`).
  `RegsProof.v` proves local kernel-checked lemmas (all closed under
  the global context): interval disjointness (`ivals_disjoint_sound`)
  and call-point exclusion (`ivals_hit_points_sound`) on well-formed
  interval lists, live-only preservation of `state_agrees` over
  registers and shared physical frame slots across caller-saved call
  and poll clobbers (`clobber_preserves_agrees`,
  `poll_edge_clobber_sound`), single- and multi-destination writes
  (`write_mach_step_sound`, `write_mach_list_sound`) and one abstract
  instruction step (`check_rinst_step_sound`), the algebraic save and
  restore round-trip (`callee_saves_restore_sound`) and non-register
  lookup of `KLower` keys (`lower_key_never_hreg`), one-step
  parallel-move source preservation (`ready_pmove_step_sound`,
  `cycle_break_step_sound`), and modular exactness of 32/64-bit `lea`
  and `imm32` selection (`imm32_congruent`, `imm32_add_mod_sound`,
  `imm32_sub_lea_w_sound`, `imm32_sub_lea_l_sound`, `-2^31` included),
  plus executable `valid_alloc` rejection examples. Full validator-to-CFG
  simulation, whole-scheduler `compile_pmoves` correctness, concrete
  frame separation and native x86 semantics are not yet proved there.
- **Behavioural gate.** `compile` and `compile-promoted` keep their
  byte-identity gates unchanged. `tests/regs.sh` (run with
  `FUGC_SCRIBBLE=1 FUGC_VERIFY=1` in the `nanofil-backend` check,
  with `tests/regs/cycles-and-spills.ir`; three planted bugs in
  call-crossing, cycle breaking and non-commutative `sub` each fail
  it) checks refusal parity and runtime agreement across the corpus:
  all 44 `difftest` files, all 9 `run-c` suites, all 228 in-subset
  `progtest` C programs, GNU hello (74 allocated units), zlib (all 17
  units), Lua 5.4.7 (all 33 non-`setjmp` units, official suite and GC
  stress) and SQLite 3.51.2 (all 3,106 functions, matching `filcc`
  output and database byte for byte, plain and under FUGC
  verification).
- **Speed.** On `rx.ir` (36 regex functions), `compile-allocated`
  emits 28,199 lines (against 45,702 for `compile-promoted` and
  28,580 for `nanofil -O compile`) in 0.30 s, and a cold cache of 39
  patterns through `rxc` takes 2.9 s (75 ms a miss, against 4.1 s
  with `compile-promoted` and 10.2 s with `nanofil -O`). Over 11
  interleaved trials on the nine benchmark patterns, the allocated
  code runs at **1.05×** of full Prolog `-O` in the geometric mean
  (0.78× to 1.17×, matching Prolog's 1.03× ablation for this pass
  set) and **0.76×** of stack-homed `compile-promoted` on this Xeon
  orb (0.61× to 0.89×; 6.5× to 22.5× faster than PCRE2's
  interpreter). On SQLite's amalgamation, lowering, allocation,
  validation and emission of all 3,106 functions take 4.6 s (against
  1.9 s for stack homes), writing 2.19M lines in place of 2.58M.

**M8. The Fil-C library.** The Crane output built by filcc as
`libnanofil` and called in the process by the pcre2 hook, which
still runs `as` and `ld` and loads with `dlopen`. Gate: the
pizlonated library passes the differential tests and the
experiment's checks.

*Not built on Crane.* M8 began, as decision 7 has it, with a
bounded attempt on the speed of Crane's C++. It went from 5 to 7.5
times the OCaml build's time to about 3, with counted references
and with a collector, and stopped there; the one filcc build that
was started did not finish compiling. The figures and what was
learnt are under [Performance targets](#performance-targets).
Crane's C++ is not taken further. The check and the C++ build
stay as they are, held to the same bytes, and `rxc` stays on the
OCaml build. What the library is built from is open: CertiRocq's C
(`rocq/backend/certirocq`, `nix/backend-certirocq.nix`) has now
been measured on the same input as well. With static literal
folding and C overrides it reaches 1.06 and 1.32 s on `rx.ir`
(3.1 and 3.2 times OCaml, matching Crane), and unlike Crane its
16 shards compile cleanly under `filcc -DVERIFFI -O1` in 143 s
and run `rx.ir` in 9.54, 8.39 and 10.40 s without Fil-C safety
errors. Lowering CertiRocq's λANF directly to nanofil IR over a
32-bit integer arena (`docs/lambda-anf.md`) is the next candidate
for a faster in-process build.

*Crane once more.* A later round on Crane's `joom/refactor`
branch reached 2 times the OCaml build natively, and its C++,
extracted file by file, compiles and runs under Fil-C, at 14 times
the native build's time. It is under
[Performance targets](#performance-targets), and its build is in
the history as [`rocq/backend/crane/joom-refactor`](https://github.com/mbrock/filnix/tree/a8083f593eeb47a6e1e919a84f53bbe718e8594f/nanofil/rocq/backend/crane/joom-refactor); the
checked build is not moved to it.

**M9. Hybrid `-O`.** Emission of the reuse forms, so Prolog's middle
end and check passes can feed the extracted backend. This is where
users of `-O` first feel the speed.

**Later.** The rest of the middle end and the check passes in
Gallina, each replacing a `*_refines` run-time check with a
theorem. An encoder and a shared-object writer, and
installing code in the process, if measurement asks for them.

**Outside this campaign.** The C frontend. It is where an everyday C
compile spends its time, so it is the thing to reconsider once the
backend is done, as its own campaign.

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
   (M4). It turned out to need no types of its own.
3. **Byte identity as the standard**, until the Gallina backend is
   the reference. Recommended: yes; it is the cheapest strong test
   there is, and the snapshot gate already works this way.
4. **The first JIT is the regex experiment's route**: `as`, `ld
   -shared` and `dlopen`, with the extracted compiler in `rxc` from
   M5. Settled by mbrock. An encoder and installing code in the
   process are later options; the second is a runtime change and
   would wait for its own review.
5. **What pcre2 needs after M5.** The first version's code has none
   of `-O`, and M5 measured what each part is worth on the nine
   benchmark patterns. Promotion with copy propagation is 2.3 times,
   registers 1.7 to 2 times, branch selection 1.1 to 1.6; the check
   passes, simplification and inlining are nothing. Recommended:
   port promotion, copy propagation and branch selection (M5b,
   done) before Crane (M6) and the allocator (M7), and leave the
   check passes and `simplify.pl` for later. Two earlier versions of this
   decision were wrong: the first credited the check passes, and the
   second took registers to be worth 1.1 to 1.7 times and put
   simplification in M5b. The other way to the same speed for pcre2
   alone is a regex compiler that emits SSA with no `alloc` slots;
   the port is preferred because every other producer of IR needs
   promotion too.
6. **How the validator gets fast.** `valid` is half of a compile
   and quadratic in a function's size, and it is the model's
   definition, with proofs that read it. Recommended: this campaign
   writes, in a file of its own, maps in place of the lists behind
   `single_definitions` and the `lookup` of a definition and of a
   class, each proved equal to the list it replaces; the model's
   owner then switches `valid_func` to them, so `valid` stays the
   same function and the proofs rewrite once. The backend takes no
   unproved replacement at extraction. Proving `valid (pizlonate m)
   = Some true`, which removes the run altogether for the first
   version, stays the later goal. *Agreed, with the equality at the
   top:* the campaign's file proves `valid_fast md = valid md`, the
   compiler runs `valid_fast`, and `valid_func` and its proofs do
   not change. `single_definitions` is done; the `lookup`s are not.
7. **What M8 does about the C++ build's speed.** M6's C++ prints the
   right bytes at 5 to 7.5 times the OCaml build's time, against a
   target of 2. That matters only in M8: on a single function the
   C++ took 4.4 times the OCaml build's time, and Fil-C's usual 1.5
   to 4 times comes on top. By that arithmetic a pattern's 16 to
   43 ms in the OCaml build would be 0.1 to 0.8 s in a pizlonated
   `libnanofil`, which is slower than starting the OCaml build as a
   process, as `rxc` does now. That is an estimate; nothing has
   been built by filcc yet. Recommended:
   keep `rxc` on the OCaml build; begin M8 with a bounded attempt
   on Crane's output (the destructor's walk, the copies of `Term`
   variants, the parameters still passed by value) with 2 times
   OCaml on `rx.ir` as the mark; and if that stalls above 3 times,
   measure CertiRocq's C on the same input before building the
   library on either. The other choice is to build `libnanofil` as
   it is, to learn first what filcc makes of Crane's C++, and take
   the speed after. *Agreed, and done:* the attempt stopped at
   about 3 times, with counted references and with a collector,
   and Crane's C++ is not taken further. CertiRocq's C
   (`rocq/backend/certirocq`) was then built and measured on the
   same input: raw it takes 8.89 and 13.77 s on `rx.ir` (165.4 s
   under `filcc -DVERIFFI`), and with static string-literal folding
   and C overrides it reaches 1.06 and 1.32 s natively (3.1 and
   3.2 times OCaml) and 9.54 and 10.40 s under `filcc -DVERIFFI`.
   Crane's `joom/refactor` branch was measured after that: 0.70
   and 0.89 s natively, which is the 2 times mark, and 9.66 and
   12.78 s under Fil-C.
