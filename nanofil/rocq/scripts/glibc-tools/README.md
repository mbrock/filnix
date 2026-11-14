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

The push gate compiles general proofs with a sealed runtime and the concrete layer's closure with a transparent interpreter. The abstract gate runs twice daily, including Hello's exact assumption comparison and an allowlist audit of every top-level proof.

`abstract-general.sh TREE OUT` checks an existing source copy with an abstract runtime. Its input has the sealed `Fix.v` binding and concrete objects previously compiled with a transparent binding. It requires exactly the failures listed in `runtime-concrete.txt` and accepts only compiler errors located in the listed files. `abstract-general-test.sh` exercises that script on small trees.

```sh
nix build -L .#checks.x86_64-linux.nanofil-glibc
nix build -L .#checks.x86_64-linux.nanofil-glibc-abstract
```
