# The glibc code generator

`generate.py` compiles captured glibc units, links their checked terms and
prints the code fixtures used by the glibc proofs. Each directory's
`code.toml` lists its units, roots and selected functions. The shell drivers
delegate to this generator; `stdio/buffer-code.sh` now checks all of `stdio`.
`gallina.pl` is unchanged.

## Regenerate or check

Build the tools and capture from the repository root:

```sh
nix build -o /tmp/filcc .#filcc-staging
nix build -o /tmp/swipl --impure --expr \
  '(import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }).swi-prolog'
nix build -L -f nanofil/survey/glibc/capture.nix -o /tmp/glibc-pp
export FILCC=/tmp/filcc/bin/clang SWIPL=/tmp/swipl/bin/swipl
```

The default command checks every directory and returns nonzero for a missing,
different or stale numbered fixture. It prints unified diffs for changed files.

```sh
nanofil/rocq/glibc/code.sh /tmp/glibc-pp
nanofil/rocq/glibc/code.sh --update /tmp/glibc-pp
```

Before cutover, pass `--legacy` to check the committed files. The default
output imports the shared prelude, which only exists in the staged tree.
Do not update the committed `.v` files on `proof-eng`. Write a separate tree
instead, or compare with a tree produced by stage 15:

```sh
nanofil/rocq/glibc/code.sh --legacy /tmp/glibc-pp
nanofil/rocq/glibc/code.sh /tmp/glibc-pp --output /tmp/generated-code
nanofil/rocq/scripts/proof-eng/check/code.sh /tmp/glibc-pp /tmp/staged-glibc
```

`--directory string` selects one directory; `--directory .` selects only
the top-level fixtures. Repeat the option to select several directories.
`--tree` selects the comparison or update destination. `--output` writes only
generated sources and the shared prelude; it never reads the comparison tree.
If the capture argument is omitted, the generator uses `/tmp/glibc-pp` or
builds `survey/glibc/capture.nix`.

## Add a unit or function

The fixture rows retain the drivers' table format:

```text
NAME|ROOTS|UNITS|FUNCTIONS[|PROGRAM]
```

`NAME` gives the output file's base name without `Code.v`. An empty roots or
units column inherits the manifest's `roots` or `units`. A `units` table uses
`OBJECT UNIT` rows; `- UNIT...` derives each object name as `glibc_` followed
by the unit basename with hyphens changed to underscores. Preserve explicit
object names, unit order and root order: the linker uses them to name private
symbols and order the resulting terms. `FUNCTIONS` lists the bodies to decode;
the libio and stdio layouts also select only those functions from the link.
`PROGRAM` names a C source relative to `nanofil`.

Existing fixtures must keep their names and presentation when units are added.
The `layout` setting chooses those conventions. The `mode` setting preserves
how each old driver compiled its units: `checked` by default, `trap` for stdlib
and `outcomes` for Len/Say.

Some linked units contain constructors that initialize the standard streams.
The `ctors` setting keeps those constructors. The stdio manifest uses a second
`[[batch]]` because its buffer fixtures come from a separate link.

The one slicer preserves whole items and blocks, with the original 500-line
getopt and 525-line hi_atexit budgets. Adding a function does not require a
new driver or slicer.

## Follow the computed-proof conversion

The regeneration check must detect changed proofs as well as changed terms.
The generator therefore takes proof styles from manifests, not from the files
it checks. Each file uses `vm_compute` unless its manifest lists another style:

```toml
[proof_styles]
"StrcmpCode.v" = "vm_cast_no_check"
```

The campaign lead is changing how Rocq checks these computed equations.
After that conversion lands on main, record which files use the new proof
style by running this helper:

```sh
python3 -I nanofil/rocq/scripts/glibc-code/sync-proof-styles.py /path/to/main/nanofil/rocq/glibc
```

This separate helper reads the tree and changes only manifests. It rejects
mixed styles within one file and unknown proof scripts before writing anything.
It does not convert proofs. Review and commit its manifest changes before
running the regeneration check.

## Integrate the check

`proof-eng/check/code.sh CAPTURE TREE` is the standalone gate entry point.
A Nix caller needs the compiler sources, these generator scripts, manifests,
fixture hashes, the checked tree, Python 3.11 or newer, SWI-Prolog, coreutils,
and `FILCC` set to the staging compiler. Supply the capture as a derivation
input; the script needs neither Nix nor network access when it receives that
path. Use the staged tree before cutover, or pass `--legacy` as a third argument
to check the old form. `nanofil/nix/glibc.nix` has not been changed.

The capture built successfully in an orb at
`/nix/store/7hh45cvwzrqyqvpknnlj82vrqdmg6kxw-filc-glibc-pp-2.44`.
The compiler came from Cachix; this capture was built locally, not substituted.
The check can therefore run in an orb and can be a dependency of the glibc
gate once its caller supplies the capture. It need not remain a manual check.
