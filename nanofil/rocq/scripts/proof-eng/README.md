# The proof-engineering pipeline for rocq/glibc

This directory holds the scripts that turn the glibc proof tree of `main` into the layout of the [proof-engineering review](https://ampcode.com/artifacts/glibc-proof-engineering-review-26baeef1-50af-4c87-b409-620bdf762969). The branch `proof-eng` carries the scripts, not their output. The output is produced again from the latest `main` each time, so campaign landings in `rocq/glibc` never need a manual merge. The output is committed once, at cutover.

## How to run it

```sh
. nanofil/rocq/scripts/proof-eng/env.sh        # rocq, Iris and the compiled model
nanofil/rocq/scripts/proof-eng/apply.sh nanofil/rocq/glibc /tmp/pe/glibc
nanofil/rocq/scripts/proof-eng/build.sh /tmp/pe/glibc 12
nanofil/rocq/scripts/proof-eng/one.sh /tmp/pe/glibc libio/LibioPutsNl.v -time
```

`apply.sh` copies the tree, runs the programs in `stages/` in name order on the copy, and then copies `overlay/` over it. It skips the stages that `stages/landed.txt` names, because their output is on `main` and a stage does not accept its own output. `build.sh` compiles the copy with make and writes times and failures to `/tmp/pe/glibc.build/`.

The workflows run on `main` only, so the Nix gates of the branch run by hand on a scratch worktree that holds the output:

```sh
nanofil/rocq/scripts/proof-eng/materialize.sh /tmp/pe-wt
nix build -L /tmp/pe-wt#checks.x86_64-linux.nanofil-glibc
```

## Stages

A stage is one program that takes the tree as its argument and rewrites it in place. The number in its name fixes the order.

- `10-flatten.py` makes every file an ordinary file over one fixed logic. On main each file is a functor over a runtime and a logic, and each importer applies it again, which costs compile time and object size. The stage removes the `XOn (R : Runtime) (LG0 : LogicSig R)` wrappers and their aliases, and a file then names a dependency by its file name. The one logic instance is in `Fix.v`.
- `15-code.py` regenerates the code modules for the flat layout.
- `20-keeps.py` moves `keeps` to the shared file `GlibcEnv.v` and rewrites the `libio/` disjunctions to it.
- `30-tactics.py` ports proofs to the one step-tactic library `GlibcTactics.v`.
- `50-program.py` removes repeated program arguments from calls between proofs. It collects their world, registry, environment and ghost instances in `GlibcProgram`, and `Defines` supplies function-lookup facts. Converted callers infer the context; old-style callers construct it with `program_of`. The forty intermediate audits listed in `check/audit-changes.json` retain their original names with equivalent bundled statements. Endpoints retain their original types and assumptions.
- `60-memory-rules.py` replaces applications of six memory rules by wrapper tactics that discharge the standard side conditions. It changes proof scripts only, and it checks that every declaration keeps its text.

The cutover is split in two, so that the flat layout could land before the later stages were ready. Stages 10 to 30 are the first cutover, which is on `main`. Stages 50 and 60 are the second cutover.

Several files define tactics with the same short name, such as `arith`. Stage `10` keeps each use bound to the definition it had before. It reorders the imports of the file when that is enough, and otherwise it writes the use with its file name, as in `StrlenLoop.arith`. The reviewed names are listed in `flatten-name-baseline.json`, and the stage fails when a new one appears.

## Regenerating the stage-50 evidence

The packet describes one source snapshot. After merging main, regenerate it from the tree of `main` with this command, after sourcing `env.sh`:

```sh
python3 nanofil/rocq/scripts/proof-eng/stages/50-program.py --regenerate nanofil/rocq/glibc
```

The command applies the stages and compiles both sides of stage 50, once at the interpreter's runtime and once at the abstract runtime. The abstract run covers every file that `runtime-concrete.txt` does not list and that imports no listed file. For each output tree it writes `50-program.txt`, `50-program.elaborated.json` and `50-program.equivalence.v` under `TREE.program/`. It retains the trees and logs under `.amp/in/orb-backup/program-regeneration-*` and prints their location. It also updates the committed declaration list for review. Generated types and proofs stay out of git; `check/audit-changes.json` preserves the forty reviewed old types and adapter mappings. Regeneration does not approve new changes or a cutover.

For a custom abstract run, `check.py partition TREE --output DIR` writes `general-targets.txt` from `runtime-concrete.txt` and the compiler's import graph. Pass that list as `PE_PROGRAM_TARGETS` with `PE_RUNTIME=abstract`; the runtime setting alone does not select the general files. Regeneration and the cutover runner do this automatically.

Run `python3 nanofil/rocq/scripts/proof-eng/stages/50-program.py --check TREE` against a converted tree to regenerate and validate its packet. The command needs the input snapshot and compiler metadata that `apply.sh` retains in `TREE.program/`. It reproduces the transformation, including the stages that run after stage 50, checks the reviewed declaration list and old types, then compiles both adapter directions. Four workers compile shards grouped by source directory, each containing at most sixteen pairs and one MiB of adapter source. Each worker has a five-minute limit.

Concrete adapters must print Closed. Abstract adapters may depend only on the declared runtime's fields: old and new statements must have identical assumption names and types, and each direction may use only a subset. The check verifies each field's identity and type with Rocq and writes the per-pair results to `TREE.program/check/assumptions.json`. Concrete success does not authorize abstract evidence; the checker requires a separate successful run for each runtime.

Stage 50 does not remove every local instance or lookup expression. Specification predicates and partial interfaces retain their parameters, while noncanonical sections retain their original setup. The stage prints each retained section and its reason. It leaves stronger program facts, absent-symbol facts and allocator premises explicit.

An inferred audited endpoint keeps its original Iris constant as an ordinary definition when its printed type needs that name. It does not register another instance.

`../glibc-code/skeleton.py` prints block-lemma statement skeletons from a manifest's linked IR. It is not a stage, and `../glibc-code/README.md` describes it.

`lint-tactics.py TREE --max N` counts the `Ltac` definitions outside the tactic libraries and the block executor `GlibcSym.v`, and fails when there are more than `N`. With `--check-inventory` it compares the tree with `tactic-inventory.json`, which lists the definitions of the tree that the stages produce from the cutover revision of main. It fails when the tree has more definitions than the list, and it prints each definition that the list does not have. `--write-inventory` records the list again after a reviewed change.

`abstract-general.sh TREE OUT` takes a flat tree that `build.sh` has compiled, and compiles a copy of it in which `Fix.v` declares `R` as an abstract `Runtime`. It passes when the files that fail to compile in the copy are exactly the files that `runtime-concrete.txt` lists, and each of them has an object in `TREE`. A listed file counts as rejected only when Rocq reports an error at a position in it: `nanofil/tests/rocq_reject.py` compiles it again and refuses a timeout, a signal, an exit status other than 1 and a library that does not load. `abstract-general-test.sh` runs the check on small trees that it must accept and reject. A file that is not listed must therefore hold for every runtime, and a file cannot be listed unless the abstract runtime rejects it. The overlay adds `runtime-concrete.txt` to the tree, and it lists one file, `hi_atexit/HiAtexitSafe.v`.

`sentence-times.py LOGS TREE` reports where a build spends its time. `LOGS` is the `sentence-timings` directory in the output of the Nix glibc gate, which holds the `rocq c -time` output of each file. Without an option the program prints the time per kind of sentence. `--file NAME` prints the slowest sentences of one file, and `--over 5` prints every sentence that took more than five seconds. `--write LIST` records the sentences over the limit, and `--check LIST` fails when a sentence over the limit is not in the list. The gate does not run the check yet.

## Rules for a stage

- A stage recognizes patterns. It never names a line number, and it names a file only when that file is the subject of the stage. The lanes add and change files every day, and the stage must convert a file it has never seen.
- A stage is deterministic, and it fails loudly on input it does not understand.
- A file written by hand goes in `overlay/` under its path in the tree. A new file belongs there. A replacement of an existing proof file belongs there only when no pattern can produce it, because a lane may change that file on `main`.
- Changes outside `rocq/glibc`, such as the Nix gate or the generators, are ordinary commits on the branch.
- Stages `10` and `30` must leave every theorem statement unchanged up to module paths. Stages `20` and `50` change the statements of intermediate lemmas on purpose. They must leave the audited top-level theorems unchanged, and the statement check lists what they changed.

## What cutover requires

The tree produced from the latest `main` passes the glibc, docs and site gates. The statement check and the Closed audits give the expected results. The campaign lead then pauses the lanes for one landing.
