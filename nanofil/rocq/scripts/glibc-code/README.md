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

The generator emits only the shared-prelude form used by the committed
fixtures. It reads the canonical `rocq/glibc/CodePrelude.v` and imports its
helpers rather than repeating them in each file. To inspect output without
updating the checkout, write a separate tree:

```sh
nanofil/rocq/glibc/code.sh /tmp/glibc-pp
nanofil/rocq/glibc/code.sh /tmp/glibc-pp --form shared-prelude --output /tmp/generated-code
```

`--directory string` selects one directory; `--directory .` selects only
the top-level fixtures. Repeat the option to select several directories.
`--tree` selects the comparison or update destination. `--output` writes only
generated sources and, in shared form, the prelude; it never reads the comparison tree.
If the capture argument is omitted, the generator uses `/tmp/glibc-pp` or
builds `survey/glibc/capture.nix`.

## Use source hints

The shared-prelude form also emits `<Name>Src.v` beside each code fixture.
Each sidecar imports its fixture and groups its tables under
`<Name>Src.fn_<symbol>`, replacing punctuation in the linked symbol with
underscores. For example, `LibioXsputnSrc.fn__IO_new_file_xsputn.loop_heads`
contains the optional cut labels for that function.

The `source` definition holds the C function's file and line, or `None` when
its context has no function location. The `block_src` table maps each located
block label to a file and line. Line numbers use binary natural numbers (`N`)
to avoid constructing long unary terms for captured files. Paths under `nanofil` are relative to that
directory, so the generated tables do not depend on the checkout location.
The generator visits phi sites, instruction sites in
index order, then the jump, and takes the first located origin. A generated
origin without a location may cite a located parent. Blocks without any
located site have no entry; the generator does not invent a function-level
fallback for them.

The `temp_names` table maps recorded temporaries to their C declaration names.
It includes only `value` records with a `named(_, value)` primary hint and
a matching binding, even when optimization has removed the temporary.
It excludes `history` records and address or piece hints.
Shadowed declarations may give different temporaries the same spelling.
The `loop_heads` list comes from `cfg.pl`'s dominators and natural-loop
analysis. It covers reachable natural loops, not every irreducible cycle.

Changing a function's blocks can leave old labels in its source tables.
The sidecar rejects those labels during compilation. One `labels_valid`
lemma uses `vm_compute` to check every function and both label tables in
the fixture. It reuses the code fixture's decoded module when available;
otherwise, the sidecar decodes the module once for all its tables.
Lazy projection extracts block labels before the boolean computation, so
the VM does not compile the decoded instruction bodies for this check.
Large fixtures put their table definitions in numbered source slices.
The main sidecar includes those definitions and performs the single membership check.
The check does not establish that a source location or C name is accurate.
The sidecars contain definitions and computed proofs, with no axioms.

Proofs must remain sound when these hints are wrong. Names and locations
serve only lemma names, stop messages and annotation keys; soundness
theorems must not take them as premises. The second executor stage accepts
any list of cut labels for `sym_func`, so it can use the generated loop
headers without trusting the analysis that found them.

The shared generator retains existing context records through the checked
stage using `cc-ir` and `bench/trap-checked.pl`; it does not change the compiler.
It passes `--context` to `link.pl`, which renames context function names
alongside local definitions and retains only surviving functions' records.
Context references neither extract archive members nor retain dead code.
Without that flag, the linker's output stays unchanged. The legacy generator
does not emit sidecars or change its compilation path.

Generate into a separate tree to leave existing code fixtures untouched:

```sh
nanofil/rocq/glibc/libio/code.sh /tmp/glibc-pp --form shared-prelude --output /tmp/generated-code
cp /tmp/generated-code/libio/*Src.v nanofil/rocq/glibc/libio/
nanofil/rocq/glibc/libio/code.sh /tmp/glibc-pp --form shared-prelude
```

The generator reports how many functions and blocks have locations and how
many recorded or current temporaries have names. It also counts natural-loop headers.
The source-table test checks that linking preserves the default bytes and
selects the right context records. It checks site order, missing locations,
recorded names and loop headers without a capture. The test driver runs this
test before its capture checks.

## Driver compatibility

All eight driver paths still accept `[--update] [GLIBC_PP]`. Checks return 0
for current files and 1 for different, missing or stale numbered fixtures.
The root driver now checks every directory instead of only Len and Say.
Both stdio drivers now check all three stdio fixtures instead of separate
groups. Their `--update` commands have the same expanded scope. Other
directory drivers keep their original scope.

The drivers print per-directory counts and unified diffs rather than their
old individual success messages. All drivers now use `/tmp/glibc-pp` if no
capture is supplied and that directory exists; root and stdlib previously
asked Nix for the capture, and getopt required an argument. `KEEP` no longer
retains temporary files. Python 3.11 or newer is required for TOML parsing.

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

Every function in a fixture row must be defined in its linked units. A missing
function fails generation and names the manifest row, rather than silently
emitting an empty decoded body. Run `test.sh CAPTURE` to check this rejection,
shared-prelude output, fixture corruption and the manifest proof-style switch.

## Start a block lemma

`skeleton.py` links one manifest fixture and prints statement skeletons for
every block of a named function. The unit argument names a directory and a
fixture row, not a captured translation unit. The function argument uses its
exact linked symbol, including the object prefix of a private function:

```sh
python3 -I nanofil/rocq/scripts/glibc-code/skeleton.py \
  getopt/Getopt 'glibc_getopt#process_long_option' \
  --capture /tmp/glibc-pp --rocq-function glibc_process_long_option
python3 -I nanofil/rocq/scripts/glibc-code/skeleton.py \
  hi_atexit/HiAtexit __GI__IO_puts \
  --capture /tmp/glibc-pp --rocq-function glibc__IO_puts --expr-type sexpr
```

A statement must name the function and expression type used by its proof.
Use `--rocq-function` to supply the function's Rocq name instead of the
placeholder `F`, and `--expr-type` to replace the default `gexpr` notation.
The author supplies these names because they belong to the proof, not the IR.
The author also supplies the runtime and logic context, memory resources,
call contracts and continuation. The command shares the generator's compilation
and linking code; it does not read proof files or write generated files.

`blocks.pl` computes the block data from the linked Prolog term. It reuses
`src/cfg.pl` for predecessor labels and backward liveness, including loop
backedges and phi operands on their particular incoming edges. The slicer
remains a text packer. Analysis follows control flow, not the order in which
blocks happen to appear in a file.

A join can read different incoming values depending on which block jumped to
it. The command therefore prints one statement for each incoming edge and adds
a lookup premise for every temporary that must already exist. It selects the
incoming phi operands before binding their results, so those results are not
entry lookups. Only the function's first block gets an entry with `None`.
An unreachable block without a predecessor gets no invented entry statement.
Poll-wrapped edges retain the underlying predecessor and target labels.

The live-out list contains names a successor may read before overwriting them.
It includes values this block defines. Such new values cannot satisfy
`keeps ks e e'` against the pre-entry environment. The output therefore also
prints an unchanged live-out list, excluding all writes and phi destinations,
and a separate list of new live-out values that need post-entry lookup facts.
These are conservative syntactic sets: they do not predict which branch runs,
infer word values, or describe memory that calls preserve. A proof may keep
additional names for its own resources or generalize a predecessor deliberately.

`--json` prints the same labels, read/write sets, live-out projections and
entry statements as structured data. Names in statement output must be printable
ASCII, with Rocq string quotes escaped. For an existing linked module term,
the analysis alone can run as `swipl blocks.pl MODULE.term FUNCTION` from this
directory. `test-blocks.py` checks edge-specific phi inputs, parallel loop phis,
dead definitions, poll edges and unreachable blocks without needing the capture.
`test.sh CAPTURE` also exercises the complete manifest-to-statement command.

## Follow the computed-proof conversion

The `[proof_styles]` table in each directory's `code.toml` is the only place
that records a generated file's computed-equality proof style. The generator
never reads that style from the files it checks, so checking catches changed
proofs as well as changed terms. Each file uses `vm_compute` unless its manifest
lists another style:

```toml
[proof_styles]
"StrcmpCode.v" = "vm_cast_no_check"
```

After converting a file's computed-equality proofs, run this command from the
repository root to record the new style in its manifest:

```sh
python3 -I nanofil/rocq/scripts/glibc-code/sync-proof-styles.py nanofil/rocq/glibc
```

This separate helper reads the tree and changes only manifests. It rejects
mixed styles within one file and unknown proof scripts before writing anything.
It requires every manifest fixture and numbered slice to be present with its
generated header. It checks multiline proofs too and does not convert proofs.
Review and commit its manifest changes before running the regeneration check.

## Integrate the check

`rocq/glibc/code.sh CAPTURE --tree TREE` checks a separate tree.
A Nix caller needs the compiler sources, these generator scripts, manifests,
fixture hashes, the checked tree, Python 3.11 or newer, SWI-Prolog, coreutils,
and `FILCC` set to the staging compiler. Supply the capture as a derivation
input; the script needs neither Nix nor network access when it receives that
path. The generator reads the canonical prelude from `rocq/glibc` and emits
shared-prelude fixtures by default. Use `--output TREE` to write a separate
tree, or `--update` to update the comparison tree.

The capture built successfully in an orb at
`/nix/store/7hh45cvwzrqyqvpknnlj82vrqdmg6kxw-filc-glibc-pp-2.44`.
The compiler came from Cachix; this capture was built locally, not substituted.
The check can therefore run in an orb and can be a dependency of the glibc
gate once its caller supplies the capture. It need not remain a manual check.
