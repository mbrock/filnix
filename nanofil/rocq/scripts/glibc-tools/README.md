# Tools for glibc proofs

This directory contains the tools used to compile and inspect the glibc proofs outside Nix. The normal Nix gates remain the checks for a change. The [migration note](MIGRATION.md) points to the retired converters in git history.

## Compile and inspect a tree

Source `env.sh` from the repository root to put Rocq, Iris and the compiled model on the shell's search paths. Set `PE_REFRESH=1` when sourcing it after changing a model theory. The script stores its tool and model links under `PE_CACHE`, which defaults to `.amp/in/scratchpad/glibc-tools`.

```sh
. nanofil/rocq/scripts/glibc-tools/env.sh
nanofil/rocq/scripts/glibc-tools/build.sh /tmp/glibc 8
nanofil/rocq/scripts/glibc-tools/one.sh /tmp/glibc libio/LibioPutsNl.v -time
```

`build.sh` compiles a source copy in dependency order and records failures, compile times and peak memory in `TREE.build/`. `one.sh` recompiles one file against objects already built beside its imports. These tools do not rewrite proofs or change the runtime binding.

`sentence-times.py LOGS TREE` reads the Nix gate's `sentence-timings/` logs. Use `--file NAME` to inspect one file or `--over 5` to list sentences taking more than five seconds. Its optional `--write LIST` and `--check LIST` record and compare a reviewed list; the gate does not run that comparison.

## Check an edit before pushing

Run `rq verify DIR/FILE.v` after saving a glibc proof. Rocq builds its imports as native interfaces and checks every proof in the selected file. To edit the model, set `PE_THEORIES=1` when sourcing `env.sh` and pass `--tree "$PE_MODEL"` to `rq verify`.

CI builds the glibc sources together against full objects. To reproduce the sealed check, run `nix build -L .#checks.x86_64-linux.nanofil-glibc`. The result contains the compiled tree under `glibc/` and the per-file logs under `sentence-timings/`. A new source must be visible to Git for Nix to include it.

## Work in a proof session

Recompiling a large proof file to see its next goal costs a minute or more. `rq/rq` keeps a Rocq session open between shell commands instead. Each session is one `rq-worker` process, which links Rocq's own parser and interpreter and keeps the state after every sentence it ran. On open and reload, Rocq lists the file’s imports and Make identifies their missing or stale `.vos` interfaces. When a build slot opens, `rq` chooses the ready interface with the longest chain of waiting dependents. The worker checks the sentences in the file you open. Interfaces live under `$PE_CACHE/rq-interfaces`. Set `RQ_JOBS` to choose the number of compiler processes (the default is eight). Use `rq open --vo` to load the existing objects beside the sources.

The first `rq open` builds the worker with `nanofil/nix/rq-worker.nix` from the same Rocq as `one.sh`.

```sh
. nanofil/rocq/scripts/glibc-tools/env.sh
rq=nanofil/rocq/scripts/glibc-tools/rq/rq
$rq open hello/HelloSetlocaleAll.v --theorem sl_find_one   # prints R1
$rq step R1 -f scratch.v          # keeps every sentence before the first failure
$rq goals R1 --conclusion         # the conclusion without the Iris context
$rq try R1 -e 'iFrame.' -e 'iFrame "H".'   # each from the same state; the session stays put
$rq check R1                      # Qed in a throwaway state
$rq reload R1                     # replay the edited file from its first changed byte
$rq verify hello/HelloSetlocaleAll.v  # check every saved proof with rocq c -vok
$rq ls; $rq stop R1
```

A step stops at the first syntax error, tactic failure or interrupt, and reports what it committed, where it stopped and the goal that remains. Its exit status is 1 when it stopped early. `rq reload` keeps the states before the first edited byte of the file. When an object that the session loaded has changed, for example after `one.sh`, it restarts the session instead. Reload drops the sentences that `step` added and saves them in the session's `dropped.v`.

Sentences have no time limit. Ctrl-C on a waiting `rq` stops only the waiting, and `rq wait R1` returns the result later. A request that is still waiting in line is withdrawn instead. `rq cancel R1` interrupts the running sentence, and the session keeps what it committed before it. The worker runs Rocq in its main domain and serves the socket from a second one, so a busy session still answers `rq status` and `rq cancel` at once. With a systemd user manager, each session is a transient service in `rq.slice`. `rq ls` then shows the memory of the whole worker tree, and `--memory-high` and `--memory-max` set the service's limits. Without a user manager, the worker runs as a detached process group, and `rq` refuses a memory limit because it could not enforce it.

A passing `rq check` does not mean that the file passes `one.sh`. The session can load interfaces that skip imported proofs, and the file on disk may differ from what the session ran. `rq --help` lists every command.

## Write a proof

Proofs share one runtime and logic instead of creating a new instance for each importer. Import `Fix.v` to obtain the sealed runtime `R` and logic `LG0`, and name dependencies by their files. Use the runtime's public laws rather than its interpreter's integer allocator state.

Calls between block lemmas need the same program and memory assumptions. The shared context carries the linked function table and the facts that remain true after each instruction. `GlibcProgram.v` defines that context, and `GlibcEnv.v` describes how instructions preserve it. Import `ProgramAbbreviations` for short names for its fields. The `Defines` instances connect function names to their bodies. A caller without a shared context can supply `(glibc_program := program_of w0 registry ge)`.

Most instruction proofs advance one instruction or discharge its access check. The shared library `GlibcTactics.v` provides these operations. Use `step` for a pure instruction and `steps` to repeat it; the symbolic, named, lookup and global variants handle less direct operands. Use `check` for access checks, the `branch` family for branches, and the `load` and `store` families for memory operations.

Loads and stores require evidence that the accessed memory belongs to the caller. The shared tactics consume that evidence, check the address and leave the next instruction for the proof. They take named ownership hypotheses and a solver after `by`; stores also take a world-preservation proof after `preserving`. A proof can apply the underlying rule directly when its side conditions differ.

To read a stored pointer, use `load_pointer` from `GlibcTactics.v`; use `load_pointer_dq` when ownership carries a fractional permission. To write a pointer, use `store_pointer` from the same library. These operations preserve the capability information attached to the pointer.

The libio proofs read character buffers and write machine words while other code may still own part of the memory. The helpers in `libio/LibioTactics.v` handle these shared reads and exclusive writes. Use `load_bytes_dq` to read a byte array and `store_word` to write a word. When only the read check remains, use `check_read_dq` to justify it from the caller's share of the buffer.

Address arithmetic needs the offsets of the fields being accessed. Each proof registers its field offsets so the arithmetic solver can replace them with numbers. For an offset called `off_field`, write `Hint Unfold off_field : offs`. The libraries offer different solvers for the remaining side conditions. Choose `concrete_side`, `libio_side` or `close_side` according to the library used by the proof.

`lint-tactics.py TREE --check-inventory` checks private tactic definitions against `tactic-inventory.json`. Proof-specific helpers may stay local; instruction tactics and memory-rule wrappers belong in the shared libraries. Use `--write-inventory` only after reviewing a change to that inventory.

## Refresh program tables

A linked program has one function table and a certificate relating its rows to the environment. After editing a table, regenerate its indexed `Defines` instances and compile the result. The refresher keeps exported instance names and adds instances for new rows.

```sh
python3 nanofil/rocq/scripts/glibc-code/refresh-tables.py nanofil/rocq/glibc
```

The [generator guide](../glibc-code/README.md) describes captured code fixtures and block-lemma skeletons. The refresher changes instances, not the generated code or the table's certificate.

## Check the runtime boundary

The push check compiles every glibc proof with a sealed runtime. Twice daily, the abstract check compiles the same tree against the runtime signature, omitting Hello’s interpreter-specific corollary.

`abstract-general.sh TREE OUT` checks an existing source copy with an abstract runtime. Its input has the sealed `Fix.v` binding, and every file must compile. `abstract-general-test.sh` exercises that script on small trees.

```sh
nix build -L .#checks.x86_64-linux.nanofil-glibc
nix build -L .#checks.x86_64-linux.nanofil-glibc-abstract
```
