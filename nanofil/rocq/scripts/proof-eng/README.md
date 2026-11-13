# The proof-engineering pipeline for rocq/glibc

This directory holds the scripts that turn the glibc proof tree of `main` into the layout of the [proof-engineering review](https://ampcode.com/artifacts/glibc-proof-engineering-review-26baeef1-50af-4c87-b409-620bdf762969). The branch `proof-eng` carries the scripts, not their output. The output is produced again from the latest `main` each time, so campaign landings in `rocq/glibc` never need a manual merge. The output is committed once, at cutover.

## How to run it

```sh
. nanofil/rocq/scripts/proof-eng/env.sh        # rocq, Iris and the compiled model
nanofil/rocq/scripts/proof-eng/apply.sh nanofil/rocq/glibc /tmp/pe/glibc
nanofil/rocq/scripts/proof-eng/build.sh /tmp/pe/glibc 12
nanofil/rocq/scripts/proof-eng/one.sh /tmp/pe/glibc libio/LibioPutsNl.v -time
```

`apply.sh` copies the tree, runs every program in `stages/` in name order on the copy, and then copies `overlay/` over it. `build.sh` compiles the copy with make and writes times and failures to `/tmp/pe/glibc.build/`.

## Stages

A stage is one program that takes the tree as its argument and rewrites it in place. The number in its name fixes the order.

- `10-flatten.py` removes the `XOn (R : Runtime) (LG0 : LogicSig R)` functor wrappers and their aliases. Files name their dependencies by file name over the one instance in `Fix.v`.
- `20-keeps` moves `keeps` to the shared logic and rewrites the `libio/` disjunctions to it.
- `30-tactics` ports proofs to the one step-tactic library `GlibcTactics.v`.
- `40-rules` replaces rule applications by wrapper tactics.
- `50-program` replaces `find_fn` premises and local `irisGS` instances by the `Defines` class and the `GlibcProgram` context.

Only `10-flatten.py` exists so far.

## Rules for a stage

- A stage recognizes patterns. It never names a line number, and it names a file only when that file is the subject of the stage. The lanes add and change files every day, and the stage must convert a file it has never seen.
- A stage is deterministic, and it fails loudly on input it does not understand.
- A file written by hand goes in `overlay/` under its path in the tree. A new file belongs there. A replacement of an existing proof file belongs there only when no pattern can produce it, because a lane may change that file on `main`.
- Changes outside `rocq/glibc`, such as the Nix gate or the generators, are ordinary commits on the branch.
- Stages `10` and `30` must leave every theorem statement unchanged up to module paths. Stages `20` and `50` change the statements of intermediate lemmas on purpose. They must leave the audited top-level theorems unchanged, and the statement check lists what they changed.

## What cutover requires

The tree produced from the latest `main` passes the glibc, docs and site gates. The statement check and the Closed audits give the expected results. The campaign lead then pauses the lanes for one landing.
