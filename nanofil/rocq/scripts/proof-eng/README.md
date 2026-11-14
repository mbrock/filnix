# The proof-engineering pipeline for rocq/glibc

This directory holds the scripts that turned the glibc proof tree of `main` into the layout of the [proof-engineering review](https://ampcode.com/artifacts/glibc-proof-engineering-review-26baeef1-50af-4c87-b409-620bdf762969). Their output is on `main`: it was produced from the latest `main` and committed at two cutovers. The scripts stay for three uses. They convert a proof file that was written in the old layout and never merged. The lint, the abstract-runtime check and the program-table refresh run on the tree as it is now. And `check/` holds the acceptance checks that compared the statements and the audits of both sides of each cutover.

## How to run it

```sh
. nanofil/rocq/scripts/proof-eng/env.sh        # rocq, Iris and the compiled model
nanofil/rocq/scripts/proof-eng/apply.sh nanofil/rocq/glibc /tmp/pe/glibc
nanofil/rocq/scripts/proof-eng/build.sh /tmp/pe/glibc 12
nanofil/rocq/scripts/proof-eng/one.sh /tmp/pe/glibc libio/LibioPutsNl.v -time
```

`apply.sh` copies the tree, runs the programs in `stages/` in name order on the copy, and then copies `overlay/` over it. It skips the stages that `stages/landed.txt` names, because their output is on `main` and a stage does not accept its own output. Every stage is listed there now, so on a tree of `main` the command only copies the overlay and checks the names. `PE_STAGES=all` runs every stage, for a tree in the layout that `main` had before the first cutover, and `PE_STAGES` can name the stages to run. `build.sh` compiles the copy with make and writes times and failures to `/tmp/pe/glibc.build/`.

The Nix gates of a converted tree run by hand on a scratch worktree that holds the output:

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

The cutover was split in two, so that the flat layout could land before the later stages were ready. Stages 10 to 30 were the first cutover and stages 50 and 60 the second. Both are on `main`.

Several files define tactics with the same short name, such as `arith`. Stage `10` keeps each use bound to the definition it had before. It reorders the imports of the file when that is enough, and otherwise it writes the use with its file name, as in `StrlenLoop.arith`. The reviewed names are listed in `flatten-name-baseline.json`, and the stage fails when a new one appears.

## Regenerating the stage-50 evidence

This section describes how the evidence for the second cutover was made. It applies to a tree that stage 50 has not converted yet, with `50-program.py` removed from `stages/landed.txt`. The packet describes one source snapshot. It was regenerated from the tree of `main` with this command, after sourcing `env.sh`:

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

## What a cutover required

The tree produced from the latest `main` passed the glibc, docs and site gates. The statement check and the Closed audits gave the expected results. The lanes were paused for each landing.
