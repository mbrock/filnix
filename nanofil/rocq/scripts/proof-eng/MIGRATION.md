# What changes for a proof author at cutover

This note is for someone who writes proofs in `nanofil/rocq/glibc/`. At cutover the output of the stages in this directory replaces the tree on `main`. Every file changes once. The statements of the audited theorems do not change. This note lists what an author writes differently afterwards and how to convert a file that is not merged yet.

The first three sections describe changes that are already on the branch `proof-eng`: flat files, the shared `keeps` definition and the one tactic library. The section on the program context describes a reviewed design that is not on the branch yet. The last section covers one open question, which is how the tree stays general in the runtime.

## Converting an unmerged file

The stages recognize patterns and do not list files, so they convert a file they have never seen. Run them on your own tree and build the result:

```sh
. nanofil/rocq/scripts/proof-eng/env.sh
nanofil/rocq/scripts/proof-eng/apply.sh nanofil/rocq/glibc /tmp/pe/glibc
nanofil/rocq/scripts/proof-eng/build.sh /tmp/pe/glibc 12
nanofil/rocq/scripts/proof-eng/one.sh /tmp/pe/glibc libio/YourFile.v -time
```

`apply.sh` replaces `/tmp/pe/glibc` with the converted copy. `build.sh` writes times and failures to `/tmp/pe/glibc.build/`, and its `make.log` ends in `DONE 0` when every file compiles. A stage fails with a message when it meets input it does not understand. Report that message instead of editing the output by hand, because the fix belongs in the stage.

## Files are flat

A file no longer wraps its content in `Module XOn (R : Runtime) (LG0 : LogicSig R)`, and it no longer instantiates its dependencies. `Fix.v` defines the one runtime `R` and the one logic instance `LG0`, and every proof file imports it. A dependency is named by its file.

Before, in `libio/LibioPutsNl.v`:

```coq
Module LibioPutsNlOn (R : Runtime) (LG0 : LogicSig R).
Module PB := LibioPutsBufOn R LG0.
Import PB PB.PM.PC.PU.PL.PI PB.PM.PC.PU.PL.PI.CS PB.PM.PC.PU.PL.PI.CS.SW PB.PM.PC.PU.PL.PI.CS.SW.FI.ML
  PB.PM.PC.PU.PL.PI.CS.SW.FI.LG PB.PM.PC.PU.PL.PI.CS.SW.FI.L PB.PM.PC.PU.PL.PI.CS.SW.OW PB.PM.PC.PU.PL.PI.CS.SW.FI
  PB.PM.PC.PU.PL.PI.CS.SW.ST.
```

After:

```coq
From Glibc Require Import Fix.
Import LibioPutsBuf LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
```

Three rules follow from this.

- A lemma's full name is its file name and its own name, as in `LibioPutsBuf.wp_buf_putc`. There is no alias chain to reconstruct.
- A new file starts with its `Require` lines, then `From Glibc Require Import Fix.`, then one `Import` line that names the files it uses. It has no `Module … On` header and no closing `End`.
- When two imported files define a tactic of the same short name, the later import wins. Write the use with its file name, as in `StrlenLoop.arith`, when you need the earlier one.

## `keeps` lives in `GlibcEnv.v`

`keeps ks e e'` says that the environment `e'` answers every name in `ks` as `e` does. It was defined in `getopt/`. It is now in `GlibcEnv.v`, which imports no other glibc file, together with `atoms`, `keeps_refl`, `keeps_put` and `keeps_trans`. The twelve `libio/` statements that spelled the same fact as a disjunction over names use it.

Before, in `libio/LibioPutsNl.v`:

```coq
⌜(forall x, x = TAtom "v0" \/ x = TAtom "v6" \/ x = TAtom "v12" \/ x = TAtom "chk1" ->
   lookup x e' = lookup x e) /\ lookup (TAtom "v208") e' = Some (WInt c)⌝
```

After:

```coq
⌜keeps (atoms ["v0"; "v6"; "v12"; "chk1"]) e e' /\ lookup (TAtom "v208") e' = Some (WInt c)⌝
```

A new block lemma states which variables it preserves with `keeps`, so that its callers can use the shared lemmas.

## One tactic vocabulary

`GlibcTactics.v` holds the step tactics, and `libio/LibioTactics.v` holds the tactics that need the stream resources. A proof file imports them and does not define its own copy. The old names are gone from the converted tree.

| Old name | New name | What it does |
| --- | --- | --- |
| `st`, `fs`, `sf`, `en`, `enter` | `step` | runs one pure instruction |
| `sl`, `sv`, `pst` | `step_symbolic` | runs one pure instruction whose value is not closed |
| `sn` | `step_named` | runs an instruction that reads a named global |
| `slk` | `step_lookup` | runs an instruction after a stated lookup |
| `st_global` | `step_global` | runs an instruction that takes a global's address |
| | `steps` | repeats `step` |
| `chk`, `fchk` | `check` | discharges an access check from a named hypothesis |
| `br`, `fbr` | `branch` | takes a branch whose condition computes |
| `sb` | `branch_symbolic` | takes a branch whose condition is not closed |
| `brv`, `fbrv` | `branch_as` | takes a branch with the stated value of its condition |
| `fbrm`, `fbrw` | `branch_rewrite` | rewrites the condition with an equation, then branches |
| `brc` | `branch_cases` | splits on the condition |
| `fldp`, `fstp` | `load`, `store` | reads or writes a pointer cell |
| `fldi`, `fsti` | `load_s32`, `store_int` | reads or writes a 32-bit cell |
| `fldn`, `fstl` | `load_null`, `store_long` | reads a null pointer cell, writes a 64-bit cell |
| `ldp`, `stp`, `ldi`, `sti`, `ldb` | `load_group`, `store_group`, `load_s32_group`, `store_int_group`, `load_byte_group` | the same accesses on a grouped ownership fact |
| `chkq`, `load_pointer` | `check_shared`, `load_shared` | the same on a fractional fact |
| `chkp`, `ldbp` | `check_persistent`, `load_byte_persistent` | the same on a persistent fact |
| `step` in `GlibcLogic.v` | `concrete_step` | runs one instruction of a closed execution |

The table is the `RENAMES` map of `stages/30-tactics.py`, which is the authority when the two differ.

Three more conventions hold.

- A field offset is registered where it is defined, with `Hint Unfold off_… : offs`. The address solvers `ar` and `a2` keep their names and unfold offsets with `autounfold with offs`, so a new field needs that one line and no change to a tactic.
- The three side-condition solvers have distinct names: `concrete_side`, `libio_side` and `close_side`. A proof names the one it needs. No file calls a bare `side`.
- `lint-tactics.py TREE --max N` counts the `Ltac` definitions outside the two libraries, and cutover fixes `N`. A helper that is specific to one proof may stay in its file. A tactic that steps an instruction or applies a memory rule belongs in the library.

## One program context (stage 50, not on the branch yet)

A rules section today takes the world, the registry, the global environment and one `find_fn` hypothesis for each function it calls, and it declares a local `irisGS` instance. After stage 50 a converted section takes one `GlibcProgram` context, and a `Defines` instance says that the program defines a function. A caller no longer passes the `find_fn` facts by position. In the trial `hge_output_overflow` passes 19 arguments where it passed 31.

Stage 50 leaves three kinds of declaration alone.

- A lemma that the audit contracts name keeps its name and its type. It becomes a wrapper that is proved from an implementation named `FILE_NAME_program`, so `Print Assumptions` on the audited name still covers the proof. Converted sections call the `_program` implementation. The stage prints every pair.
- A specification predicate such as `overflow_spec` keeps its original parameters.
- A section that is partial or pure keeps its original interface, so that it gains no ghost-state or world premise. The stage prints each such section with its reason.

## What is not decided: generality in the runtime

`hello_never_panics` holds for every `Runtime`, and the audit checks that by listing twelve runtime assumptions. `Fix.v` therefore has two forms. The stages write `Module R := InterpRuntime.` by default, and with `PE_RUNTIME=abstract` they write `Declare Module R : Runtime.`. A file that does not depend on `InterpRuntime` compiles against both.

Until the layout is chosen, keep to one rule that holds under every option: a file names `InterpRuntime` only when its theorem is about the interpreter, as the `hi_atexit` endpoints are. Every other file uses `R` and `LG0` from `Fix.v` and nothing that is specific to the interpreter.
