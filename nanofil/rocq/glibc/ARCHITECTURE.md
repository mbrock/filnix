# Architecture of `nanofil/rocq/glibc/`

This tree currently holds three distinct bodies of Rocq code under one build root:

1. **Shared userland C and OS proof infrastructure** (`base/`, `zsys/`, `tactics/`, and the root foundation files migrating into them): the runtime logic instantiation, the Linux/Fil-C syscall world, generic memory and stepping tactics, C-struct lenses, reflective symbolic execution, and ELF image-piece helpers. None of this is specific to glibc; any Fil-C C library or program proof uses it.
2. **glibc 2.44 library proofs** (`string/`, `nptl/`, `stdlib/`, `locale/`, `intl/`, `libio/`, `stdio/`, `getopt/`, `startup/`, and generated captures under `gen/`): library proofs parameterized over the program context (`GlibcProgram`), never referencing a specific binary.
3. **Whole-program proofs** (`hello/`, `hi_atexit/`): concrete programs linked against glibc, isolated from sibling programs.

New and promoted shared modules should be named for what they prove (`OsMemLogic`, `OsTactics`, `ImagePieces`, `LiteralLogic`, `ByteRead`) rather than prefixed with `Glibc`.

## A living map, not bureaucracy

The declarative layer map lives in [arch.json](arch.json) and is checked by [proof_arch_check.py](../../tests/proof_arch_check.py). Treat it as a pragmatic tripwire against accidental drift during fast multi-agent work, not as rigid red tape. When the checker fires, there are always two valid responses:

1. Fix the accidental tangle (a stray import, a helper sitting in a top-of-tower proof file, or a private tactic missing `Local`).
2. Consciously revise [arch.json](arch.json) when real C semantics or proof engineering genuinely call for a different boundary, and record the reason in the commit message.

## Layer map

Dependencies point downward through six layers (with sibling programs in `L5` isolated from one another):

- **L0 — Pure IR and data:** generated captures under `gen/` plus pure IR, layout, and piece modules in `base/`. Nothing in L0 imports Iris, `Fix`, or `zsys`.
- **L1 — Logic and OS foundation:** `base/`, `zsys/`, and legacy root foundation files. This layer holds the single canonical Nanofil functor instantiation in `Fix*.v`, the OS syscall world in `OsWorld` and `OsRegistry`, the program context in `GlibcProgram` and `GlibcSpec`, and generic OS-world memory and literal rules such as `OsMemLogic`, `ByteRead`, and `LiteralLogic`.
- **L2 — Shared proof infrastructure and tactics:** `tactics/`. This layer holds pure stepping tactics in `GlibcTactics`, generic OS-world memory tactics in `OsTactics`, C-level lenses in `CFrame`, `CStruct`, and `CBlocks`, and opt-in reflective symbolic execution in `GlibcSym*`. Nothing in L1 or L2 imports `FileInv` or `libio/`.
- **L3 — glibc library subsystems**, ordered as a DAG:
  - **L3a:** `string/`, `nptl/`, `stdlib/`
  - **L3b:** `locale/`, `intl/`
  - **L3c:** `libio/` (`FileInv` and `FILE`-specific stream proofs)
  - **L3d:** `stdio/`, `getopt/`
- **L4 — Generic startup** (`startup/`): reusable `__libc_start_main`, constructors, and initialization parameterized over an image, with no dependency on `hello/` or `hi_atexit/`.
- **L5 — Whole-program proofs** (`hello/`, `hi_atexit/`): concrete images, wiring, and top-level safety theorems.

## Functor policy

Rocq functor applications copy definitions and lemmas into the compiled `.vos` interface of every module that instantiates them. Instantiate each Nanofil functor once:

- `Fix.v` owns `R`, `LG0 := Logic R`, `ML0 := MemLogicOn R LG0`, and `SL0 := StringLogicOn R LG0`.
- `FixVariadic.v` owns `VL0 := VariadicLogicOn R LG0`, keeping variadic definitions off the import path of ordinary files.
- `FixExec.v` owns `AS0 := AbsSoundOn R LG0`, keeping abstract-execution soundness off ordinary Iris proofs.

Proof files import from `Fix*` directly instead of re-instantiating functors or aliasing `FileInv.ML`.

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

## Cleanup phases

1. **Phase 0 (current):** declarative map in `arch.json`, ratcheted checker in CI, and baseline measurement.
2. **Phase 1:** consolidate functors into `Fix*.v`, extract generic OS-world memory rules into `base/OsMemLogic.v`, move root foundation files into `base/` and `tactics/`, and detach `CStruct.v` from `FileInv`.
3. **Phase 2:** create `tactics/OsTactics.v`, slim `libio/LibioTactics.v` to `FILE` tactics, extract bottom-of-subsystem `*Tactics.v` files, and mark proof-file tactics `Local`.
4. **Phase 3:** promote misplaced common goods (`ImagePieces`, `LiteralLogic`, `ByteRead`, `AllocCall`) and close backward edges into `hello/` and `hi_atexit/` as well as upward library edges.
5. **Phase 4:** prune duplicate and unused `Require` statements across the tree.
6. **Phase 5:** re-measure cold and warm `rq open` timings, selectively shape any remaining serial micro-file spines where readability also improves, and layer `rq` scheduling improvements on top.
