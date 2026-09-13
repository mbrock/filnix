# Selecting packages to try with Fil-C

The inventory is a practical discovery list: find more programs and libraries
that work on the Filnix platform. It is not an estimate of the fraction of all
software that Fil-C supports. Uncertain C/C++ builds belong in the experiment.

Run the selection without building packages:

```sh
python3 scripts/package-inventory.py --output results/package-inventory
```

For a small sample, add `--packages hello jq ripgrep python3 libvpx`. Resume an
interrupted collection with the same arguments plus `--resume`. Reapply the
current selection policy to saved observations with `--report-only`; this does
not invoke Nix. Use a new output directory to preserve an earlier selection.

## Scope and decisions

The initial universe is the sorted top-level attribute names of native
`x86_64-linux` Nixpkgs at the repository's locked input. Deprecated aliases are
disabled. Nested collections such as `python3Packages`, `haskellPackages`,
`perlPackages`, and `libsForQt5` are recorded as collections, not recursively
expanded. Their top-level exports can still appear. Other aliases and package
variants remain separate attributes until a later derivation planning stage.

Metadata evaluation permits inspecting broken, unsupported, unfree, and insecure
recipes; this is not a change to Filnix's build policy. Non-Linux packages and
clear active Rust, Go, Haskell, OCaml, .NET, or Dart builders are excluded. The corresponding
self-hosting compiler implementations, Zig, Erlang, Linux kernels, and declared
prebuilt code are also outside this first list. Other languages may remain as
false positives: evidence is deliberately incomplete and reviewable.

Source packages with a C/C++ standard environment are candidates. Active
Python/Node package builders and other-language compiler clues make a possible
C/C++ build uncertain, and **uncertain packages are selected too**. CPython,
Perl, Ruby, Lua, Tcl, and other interpreters implemented in C/C++ remain ordinary
candidates. Using a Rust-built tool such as cbindgen or a Python code generator
does not make the resulting package a Rust or Python implementation.

Declaring `cargoDeps` alone also does not exclude a package: Ruby uses it for
YJIT. A Rust dependency declaration with the active Cargo build hook is a clear
Rust build; without that hook, it is retained as uncertain and annotated. This
intentionally admits some Rust programs with custom build systems as well as
C/C++ programs with optional Rust components.

Packages without source or compilation evidence, including wrappers, data and
many script-only applications, are deferred. Evaluation failures are retained as
unresolved. Native `meta.broken` and disabled checks add information without
excluding an otherwise plausible candidate.

## Assembly, dependencies, and tests

Assembly and JIT mentions in the packaging expression and adjacent patches are
annotations, never exclusion rules. `nasm` and `yasm` build inputs are recorded
separately. This includes disabled assembly paths: the stored file, line, and
excerpt let a reader interpret the clue. Large generated/shared expressions are
not scanned as though all their contents belonged to one package. No upstream
source trees are fetched or inspected, so a missing tag proves nothing about
the package's use of assembly.

Direct native/build/propagated/check input names retain their roles. This is not
yet a transitive dependency audit, and no claims about a dependency's language
are made from its name alone. The check flags describe the native Nixpkgs recipe;
they do not establish that checks will run under Filnix or that any tests passed.

## Execution and artifacts

One Nix evaluator runs at a time, with a default 4 GiB virtual-address-space
limit, affinity to at most two hardware threads, and a 45-second batch timeout.
Failures split a batch until the problematic attribute can be recorded on its
own. Import-from-derivation is disabled, local build jobs are zero, remote
builders are disabled, and evaluation uses the already available pinned input
offline. Nothing changes the daemon configuration or starts a package build.

The collector deliberately avoids derivation/output paths and source contents.
Its Nix expression is independent of the Filnix ports overlay. Filnix revisions
and local tracked changes are recorded as context for later experiments.

Each output directory contains:

- `run.json`: pin, complete attribute universe, evaluator hash and resource limits.
- `metadata.jsonl`: raw observations, including incomplete fields and errors.
- `inventory.jsonl`: every decision, reason, annotation, and source excerpt.
- `candidates.json`: explicit attribute paths, policy/metadata hashes, and counts.
- `candidates.txt`: readable top-level attribute names, one per line.
- `REPORT.md`: counts, examples, and interpretation limits.
- `diagnostics.jsonl`: evaluator diagnostics, including batch failures.
- `evaluator.nix`, `policy.py`, `filnix-context.patch`: the collection expression,
  classification code, and tracked local changes at collection time.

The manifest uses arrays for attribute paths, so a literal dot in a top-level
name is not confused with descent into a nested package set. Downstream tooling
should consume `candidates.json`, not interpolate text lines into shell commands.

Validate the selector and its no-build boundary with:

```sh
python3 tests/package-inventory.py
```
