# What changes for a proof author at cutover

This note is for someone who writes proofs in `nanofil/rocq/glibc/`. At cutover the output of the stages in this directory replaces the tree on `main`. Every file changes once. The audited endpoints keep their statements. This note lists what an author writes differently afterwards and how to convert a file that is not merged yet.

The first three sections describe the first cutover, which is on `main`: flat files, the shared `keeps` definition and the one tactic library. The sections on the program context and on the memory-rule tactics describe the second cutover, which adds stages 50 and 60. The last section says how the tree stays general in the runtime and what that asks of an author.

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
- `lint-tactics.py TREE --check-inventory` counts the `Ltac` definitions outside the two libraries and the block executor `GlibcSym.v`, and fails when the tree has more than `tactic-inventory.json` lists. The list is recorded from the tree that lands at cutover. A helper that is specific to one proof may stay in its file. A tactic that steps an instruction or applies a memory rule belongs in the library.

## One program context (stage 50, second cutover)

A converted rules section takes one `GlibcProgram` context instead of separate world, registry, environment and ghost-state parameters. Its Iris instance comes from that bundle. A `Defines` instance supplies each function-lookup fact, so callers no longer pass those facts by position.

Import `ProgramAbbreviations` once in a converted file to use `w0`, `registry` and `ge`. A converted caller writes `iApply (wp_live_fit1 with "Hl")`; instance search supplies its program. An old-style caller supplies `(glibc_program := program_of w0 registry ge)` when applying a bundled rule. A converted proof can still use an old-style rule: `Defines` is the same lookup equality, and the bundle provides its original world and ghost instances.

The forty audited intermediate declarations listed in `check/audit-changes.json` take bundled statements under their original names. They have no compatibility wrappers. The packet records their full old and new types and proves both directions with the same resources and ghost instances. Every endpoint retains its name, type and assumptions; the permission applies only to the listed file/name pairs.

Specification predicates such as `overflow_spec` retain their parameters. Partial and pure interfaces gain no world or ghost-state premise, and noncanonical sections keep their existing setup. The stage prints retained sections with their reasons. Stronger program facts and allocator premises remain explicit.

A linked program has one function table and one computed certificate. After editing a table, run `python3 nanofil/rocq/scripts/proof-eng/stages/50-program.py --refresh-tables TREE` and compile it again. The command generates the indexed instances from the rows; authors do not maintain a second list.

The [README](README.md#regenerating-the-stage-50-evidence) gives the single regeneration command for the three packet files, which are build outputs rather than committed pages. Run it after merging main and review the resulting declaration list and types. `50-program.py --check TREE` regenerates evidence from the retained input, verifies the transformation, and compiles the adapters in bounded parallel shards. It preserves the reviewed old types of the forty intermediate audits and checks each runtime separately.

## Memory rules have wrapper tactics (stage 60, second cutover)

A load, a store or a read check applies one memory rule and then discharges the same side conditions each time: the instruction's shape, the value, the capability and the address arithmetic. Six tactics apply the rule and discharge those conditions. The proof names the ownership hypotheses and the one solver that differs between uses.

Before, in `getopt/GetoptColon.v`:

```coq
iApply (wp_raw_load_pointer_dq with "Hl Hnext Hcc");
  [reflexivity | vx | left; reflexivity | arith | arith | lia |].
iApply (wp_check_read_dq registry (os_wi w0) ge with "Hcl");
  [reflexivity | vx | exact Hccap | arith | arith | arith |].
iApply (wp_raw_load_sub_bytes_dq with "Hcl Hct");
  [reflexivity | vx | reflexivity | apply extended_chr | exact Hccap | arith |].
```

After:

```coq
load_pointer_dq "Hl Hnext Hcc" by arith.
check_read_dq "Hcl" by arith.
load_bytes_dq "Hcl Hct" decode (apply extended_chr) by arith.
```

| Tactic | Rule | Library |
| --- | --- | --- |
| `load_pointer H by side` | `wp_raw_load_pointer` | `GlibcTactics.v` |
| `load_pointer_dq H by side` | `wp_raw_load_pointer_dq` | `GlibcTactics.v` |
| `store_pointer H by side preserving world` | `wp_raw_store_pointer` | `GlibcTactics.v` |
| `check_read_dq H by side` | `wp_check_read_dq` | `libio/LibioTactics.v` |
| `load_bytes_dq H decode d by side` | `wp_raw_load_sub_bytes_dq` | `libio/LibioTactics.v` |
| `store_word H by side preserving world` | `wp_raw_store_w` | `libio/LibioTactics.v` |

A wrapper leaves the rule's continuation as the one remaining goal, as the `iApply` did, so the `iNext` and `iIntros` that follow stay as they were. The stage converts an application only when its side conditions have the standard shape. An application with another solver in some position keeps its `iApply`, and a new proof may write either form.

## Proofs stay general in the runtime

`hello_never_panics` holds for every `Runtime`, and the audit checks that by listing twelve runtime assumptions. `Fix.v` binds `R` to `InterpRuntime`, so the ordinary build checks every file at the interpreter's runtime only. Two more checks compile files against a copy of `Fix.v` that says `Declare Module R : Runtime.` in place of the binding:

- Every push checks Hello's theorem. The glibc check compiles the files that the theorem depends on a second time, with the runtime left abstract. Rocq must then report exactly the twelve fields of the runtime as the theorem's assumptions.
- Twice daily, the check `nanofil-glibc-abstract` compiles every file that `rocq/glibc/runtime-concrete.txt` does not list. At the first cutover the list names one file, so the check compiles every other file.

An author follows three rules:

- An author writes against the runtime that `Fix.v` names and relies on nothing that is true only of the interpreter. The ordinary build cannot check this rule, because it compiles every file at the interpreter. It accepts, for example, a proof that writes a number where the runtime's state is expected. If Hello's theorem does not depend on the file, the push check accepts the proof too, and the twice-daily check fails later.
- A file may name `InterpRuntime` when its theorem is about the interpreter, as the `hi_atexit` endpoints are. Naming the module does not make a file concrete. Seven of the eight files that name it compile against the abstract runtime, because they do not need `R` to equal it.
- A file that needs `R` to be the interpreter's runtime goes into `runtime-concrete.txt`, with a comment that gives the reason. Every file that imports a listed file must be listed too. The one listed file is `hi_atexit/HiAtexitSafe.v`, whose theorem starts the interpreter at a numeric allocation cursor.

The list cannot hide a failure of another kind. The check compiles each listed file against the abstract runtime and requires Rocq to report an error at a position in that file. It fails when a listed file compiles, and it does not accept a timeout, a killed compiler or a library that does not load as a rejection.

Run the check on your own tree before you push a file that touches the runtime. The script works on a copy that `build.sh` has compiled, so that no object file is written into the checkout:

```sh
. nanofil/rocq/scripts/proof-eng/env.sh
mkdir -p /tmp/general && cp -r nanofil/rocq/glibc /tmp/general/glibc
nanofil/rocq/scripts/proof-eng/build.sh /tmp/general/glibc 8
nanofil/rocq/scripts/proof-eng/abstract-general.sh /tmp/general/glibc /tmp/general/abstract 8
```

It prints one `FAIL` line for each file on the wrong side of the list. The same check in Nix is `nix build -L .#checks.x86_64-linux.nanofil-glibc-abstract`.
