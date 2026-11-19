# Architecture of `nanofil/rocq/glibc/`

The glibc proof tree has three parts. Rocq builds them under one logical root.

1. **Shared userland C and OS proof infrastructure** (`base/`, `zsys/`, `tactics/`): the runtime logic instantiation, the Linux/Fil-C syscall world, generic memory and stepping tactics, C-struct lenses, reflective symbolic execution, and ELF image-piece helpers. None of this is specific to glibc; any Fil-C C library or program proof uses it.
2. **glibc 2.44 library proofs** (`string/`, `nptl/`, `stdlib/`, `locale/`, `intl/`, `libio/`, `stdio/`, `getopt/`, `startup/`, and generated captures under `gen/`): library proofs parameterized over the program context (`GlibcProgram`). The wide-character conversion proofs also use the C locale placement table generated from Hello.
3. **Whole-program proofs** (`hello/`, `hi_atexit/`): concrete programs linked against glibc, isolated from sibling programs.

New and promoted shared modules should be named for what they prove (`OsMemLogic`, `OsTactics`, `ImagePieces`, `LiteralLogic`, `ByteRead`) rather than prefixed with `Glibc`.

## A living map, not bureaucracy

The declarative layer map lives in [arch.json](arch.json) and is checked by [proof_arch_check.py](../../tests/proof_arch_check.py). Treat it as a pragmatic tripwire against accidental drift during fast multi-agent work, not as rigid red tape. When the checker fires, there are always two valid responses:

1. Fix the accidental tangle (a stray import, a helper sitting in a top-of-tower proof file, or a private tactic missing `Local`).
2. Consciously revise [arch.json](arch.json) when real C semantics or proof engineering genuinely call for a different boundary, and record the reason in the commit message.

## Layer map

Dependencies point downward through six layers (with sibling programs in `L5` isolated from one another):

- **L0 — Pure IR and data:** generated captures under `gen/` plus pure IR, layout, and piece modules in `base/`. Nothing in L0 imports Iris, `Fix`, or `zsys`.
- **L1 — Logic and OS foundation:** `base/`, `zsys/`, and shared image rules. This layer holds the single canonical Nanofil functor instantiation in `Fix*.v`, the OS syscall world in `OsWorld` and `OsRegistry`, the program context in `GlibcProgram` and `GlibcSpec`, and generic OS-world memory and literal rules such as `OsMemLogic` and the registry predicates in `OsExternals`.
- **L2 — Shared proof infrastructure and tactics:** `tactics/`. This layer holds pure stepping tactics in `GlibcTactics`, generic OS-world memory tactics in `OsTactics`, C-level lenses in `CFrame`, `CStruct`, and `CBlocks`, and opt-in reflective symbolic execution in `GlibcSym*`. Nothing in L1 or L2 imports `FileInv` or `libio/`.
- **L3 — glibc library subsystems**, ordered as a DAG:
  - **L3a:** `string/`, `nptl/`, `stdlib/`
  - **L3b:** `locale/`, `intl/`
  - **L3c:** `libio/` (`FileInv` and `FILE`-specific stream proofs)
  - **L3d:** `stdio/`, `getopt/`
- **L4 — Generic startup** (`startup/`): reusable `__libc_start_main`, constructors, and initialization parameterized over an image, with no dependency on `hello/` or `hi_atexit/`.
- **L5 — Whole-program proofs** (`hello/`, `hi_atexit/`): concrete images, wiring, and top-level safety theorems.

## Option tables and image proofs

Hello's option table can be checked as soon as its captured object and the table schema are available. `LongOption` describes the option fields and return codes. `LongOptionTable` describes the memory a caller lends to the parser. The exact-match loop, flag store and parser call proofs consume those definitions. The startup proof supplies the implementation of the getenv call through `GetenvSpec`.

`GetoptMessageData` holds the nine format strings and their symbol names. `LiteralLogic` proves that literals at distinct bases occupy distinct heap pieces and turns those pieces into shared strings. Both the image check and the diagnostic call proofs use those facts. `ImageData` checks loader symbol addresses and reads global initializers for the constructor, diagnostic and stream image checks.

`HelloObjects` gives startup and main the same description of the linked globals. `HelloNameOffsets` specifies which bytes of argv[0] name the program, and `PrintfTables` describes the formatter globals that main shares. A proof of the image layout can use these contracts without loading the code that runs main, chooses a program name or prints a string.

## Functor policy

Rocq functor applications copy definitions and lemmas into the compiled `.vos` interface of every module that instantiates them. Instantiate each Nanofil functor once:

- `Fix.v` owns `R`, `LG0 := Logic R`, `ML0 := MemLogicOn R LG0`, and `SL0 := ML0.SL`.
- `FixVariadic.v` owns `VL0 := VariadicLogicOn R LG0`, keeping variadic definitions off the import path of ordinary files.
- `FixExec.v` owns `AS0 := AbsSoundOn R LG0`, keeping abstract-execution soundness off ordinary Iris proofs.

Proofs use the instances from `Fix*`. The memory logic already instantiates the string logic, so `SL0` names that same instance.

## Tactic hierarchy

- **Tier 1 (universal tactics in `tactics/`):** `GlibcTactics` (pure IR stepping over `Fix`), `OsTactics` (generic OS-world memory loads, stores, and capability checks over `OsMemLogic` without `FileInv`), `CFrame`/`CStruct`/`CBlocks`, and opt-in `GlibcSym*`.
- **Tier 2 (subsystem tactics):** at most one `*Tactics.v` module per library directory (`libio/LibioTactics.v`, `string/StringTactics.v`, `getopt/GetoptTactics.v`), sitting at the bottom of that directory so branch proofs compile in parallel.
- **Tier 3 (file-private tactics):** every `Ltac` or `Tactic Notation` defined inside an ordinary proof file must be `Local`.

## Running the checker

```bash
# Check against the ratcheted baseline in arch.json
python3 nanofil/tests/proof_arch_check.py

# Print the full debt breakdown and critical-path depths
python3 nanofil/tests/proof_arch_check.py --report

# Tighten the ratchet after a cleanup phase removes violations
python3 nanofil/tests/proof_arch_check.py --update-baseline
```

## What the checker measures

The layer check covers direct imports, including imports between the two program directories. Startup reads CPU function bodies from the capturing translation units. Each program proves that its own linked image contains those bodies. The string library owns buffer copying and wide-character byte reads. The stream library owns the write contracts that both formatters and whole programs use.

Each ordinary proof should keep a tactic local when all its callers are in that file. Some older files also supply tactics to other proofs. The manifest records the remaining count while those callers migrate to subsystem tactic modules.

The import check counts a direct import as a candidate for removal when its exported names do not occur in the file. An import can still supply a notation, a hint, a typeclass instance or a name through a re-export. Compile the dependent proofs when removing a candidate.

For a cold-open measurement, give `rq` an empty interface cache, a prebuilt worker and a fixed `RQ_JOBS`, then open a named theorem. For a warm measurement, stop the worker and open the same theorem again with the same cache. The architecture report counts each reachable glibc interface once and gives the longest chain in files, including the target. The elapsed time also depends on the cost of each file and when its compiler can start.
