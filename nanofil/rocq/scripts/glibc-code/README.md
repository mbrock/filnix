# The glibc code generator

`generate.py` compiles captured glibc units, links their checked terms and
prints the code fixtures used by the glibc proofs. Each directory's
`code.toml` lists its units, roots and selected functions. The shell drivers
delegate to this generator; `stdio/buffer-code.sh` now checks all of `stdio`.
`gallina.pl` prints the transport terms that the smaller fixtures decode.

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
fixtures. It reads the canonical `rocq/glibc/CodePrelude.v` for fixtures that store raw terms. To inspect output without
updating the checkout, write a separate tree:

```sh
nanofil/rocq/glibc/code.sh /tmp/glibc-pp
nanofil/rocq/glibc/code.sh /tmp/glibc-pp --form shared-prelude --output /tmp/generated-code
```

`--directory string` selects one directory; `--directory .` selects only
the top-level fixtures. Repeat the option to select several directories.
`--tree` selects the comparison or update destination. `--output` writes only
generated sources and the shared prelude and notation modules; it never reads the comparison tree.
If the capture argument is omitted, the generator uses `/tmp/glibc-pp` or
builds `survey/glibc/capture.nix`.

## Source hints

Source hints are what the glibc proofs learn about the C source of a
compiled function. Nanofil's C front end keeps context records beside each
checked function body (`src/provenance.pl`) and can print the completed C
layouts (`src/c_layouts.pl`). The generator reads both, together with the
compiler's control-flow and liveness analyses, and writes Rocq tables beside
each code fixture. The proofs use these tables to name temporaries, fields,
lines and cut points.

The proofs never trust a source hint. Only the checked IR in the code fixture
is proved about, and a soundness theorem must not take a hint as a premise.
Compilation checks that every label a hint cites belongs to the decoded
function, but it does not check that a name, path or location is accurate.

The generator writes four kinds of source hint, described in the sections
below. Source tables give locations, C names and loop headers. Names give
notations for temporaries. Block facts give liveness and memory footprints.
Layouts give the fields of C records.

## Use source tables

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
The `temp_keys` table says which C value each temporary of the body holds.
A row `(t, (root, key, offset))` says that `t` holds the value of `root`, moved
by `offset`. A check holds the pointer it checked, and a constant pointer
addition holds its operand moved by the constant, so both follow their operand
to its root. The walk stops at a temporary with a hint of its own. The key of a
root with a `named(_, value)` hint is the declaration name, and the key of a
root with a `named(_, address)` hint is `&` and the name. A root without a hint
has its own name as the key; these are the fallbacks. A temporary without a row
is its own root. `CFrame.v` builds the signature of a cut from this table and
the label's `live_in` row. For each function the generator prints the number of
temporaries in the body and how many are named, hold an address, are derived
from a keyed root, or fall back.
The `loop_heads` list comes from `cfg.pl`'s dominators and natural-loop
analysis. It covers reachable natural loops, not every irreducible cycle.

Changing a function's blocks can leave old labels in its source tables.
The sidecar rejects those labels during compilation. One `labels_valid`
lemma uses `vm_compute` to check every function and all label tables in
the fixture. It reuses the code fixture's decoded module when available;
otherwise, the sidecar decodes the module once for all its tables.
Lazy projection extracts block labels before the boolean computation, so
the VM does not compile the decoded instruction bodies for this check.
Large fixtures put their table definitions in numbered source slices of about 100 KB.
The main sidecar includes those definitions and performs the single membership check.
Source and block facts share these slices, so only the main sidecar imports the decoded module.
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
Without that flag, the linker's output stays unchanged.

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

## Name temporaries after C expressions

A batch with `names = true` also gets `<Name>Names.v` beside each fixture.
It holds one module per function, `<Name>Names.fn_<symbol>`, and each module
holds one notation per temporary that has a C expression. A proof imports the
module of its own function. It can then write `‹buf+8›` where it would write
`TAtom "v8"`, and Rocq prints goals with the same names. A notation changes
only how a term is written and printed, so tactics that match
`lookup (TAtom t) e` work as before, and a wrong name can only make a lemma
harder to read.

Every name is one token between single guillemets. Without them Rocq would
read `s+192` as the temporary wherever the module is imported, even in a
statement about an integer `s`. The site's grammar reads a guillemet name as
one name too. Do not write these names without the guillemets.

The names come from the `temp_shapes` rows of `source.pl` and the field paths
of the block footprints:

| Temporary | Name |
| --- | --- |
| holds a C variable | `‹buf›` |
| holds a variable's or a global's address | `‹&wrap›` |
| constant pointer addition | `‹buf+8›` |
| check of a pointer | `‹chk(buf+8)›` |
| load of a field the layouts name | `‹buf->write_ptr›` |
| load without a field path | `‹[buf->fp+216]›` |
| address of a pointer as an integer | `‹addr(format)›` |
| comparison | `‹s->_mode==0›` |
| result of a direct call | `‹__printf_buffer_to_file_done()›` |

Arithmetic, phis without a hint and results of indirect calls have no name,
and neither does anything computed from them.

The compiler often computes one C expression again in a later block. The
first temporary gets the plain name. A later one gets `@` and the label of
its block, such as `‹buf+8@L4›`, and a further one in the same block gets
`‹buf+8@L4.2›`. Only these ambiguous names carry a suffix. The suffixes follow
the compiler's label numbering, so a recompile that renumbers labels changes
them. New proofs state their frames with `c_env` keys, which do not depend on
labels, and use these names for reading goals and for the statements of
lemmas about single instructions.

The stdio printf batches turn names on. Another batch opts in when someone
next works on its proofs. The two whole-image fixtures have no source tables,
so they have no names. For each function the generator prints how many names
come from a hint, how many are derived, how many carry a suffix and how many
temporaries stay unnamed.

## Use block facts

An executor can forget a temporary once no later block can read it.
Doing so only weakens its claim about the symbolic environment.
Each fixture's `<Name>Src.v` records which values remain live at each
block boundary, in the same function modules as its names and locations.

A block may select a different value from each incoming branch.
Its phi arguments are uses on those edges, while phi destinations are definitions at entry.
The `live_in` and `live_out` tables come from `cfg.pl`.

An executor needs to know which pointer and byte range a block accesses.
The `footprint` table gives the address and constant byte offset for each
explicit access, in instruction order. Each entry also records the zero-based
instruction index, byte width and read and write flags.

Readable stops need field names rather than byte offsets. The last footprint
component is a string path such as `fp->_IO_write_ptr`, `fp->_lock->owner`
or `fp->embedded.owner`. The string `opaque` means that neither source
origins nor a complete layout resolved the access.

Casts can make a pointer refer to a different record type. When the source
names a field through a cast, a stop message should retain that field name.
The generator therefore prefers a unique source path over a lookup using
the pointer's declared type. The printed path omits the cast. Reading a
pointer field and following the stored pointer describe different accesses.

When the source expression does not identify a field, a constant offset
may still select one from a complete C layout. The generator walks embedded
records with their own offsets and treats a loaded pointer as a new root.
Record numbers belong to one translation unit. The generator matches each
linked function's context to its original unit before reading those numbers.

Ambiguous union members require a selecting source expression. Padding,
unresolved arithmetic and unresolved subscripts remain `opaque`; the generator
does not guess a nearby field. Paths support stop messages and annotation
keys only. They add no premise to a soundness theorem, and compilation
checks only their enclosing block labels, not their source accuracy.

An address computed by advancing another pointer can still refer to that
pointer's object. The table records this root temporary and the constant
distance from it when known. Flight lower donors and the existing guard-chain
analysis supply this information. Checked proof operands resolve to their
pointer or local object.

Some byte ranges depend on values known only when the program runs.
Unknown widths and pointer distances use `None` rather than invented constants.
The generator does not infer accesses inside called functions.
A proof may use these hints to choose candidate memory regions,
but it must justify each access without trusting them.

Compilation rejects labels that are not blocks of the decoded function.
The shared `labels_valid` lemma performs this check once per fixture, using
the decoded module's block labels. The generator projects labels before compiling
the membership computation, so temporary sets and access records stay out
of its VM code. Large fixtures split definitions into numbered files by
size, while the main file retains the single check.

The generator reports block counts, liveness entries, accesses, resolved roots and path coverage.
`test-block-facts.py` checks phi edges, local objects, byte widths and the
difference between constant and dynamic root offsets through the analysis command.
It also checks nested field paths, layout-only recovery, union ambiguity,
translation-unit scoping and accesses through loaded buffer pointers.

The tables do not describe which earlier range checks remain available at a block's exit.
The check-reuse pass calculates those `avail` facts but discards its exit maps.
Later passes also rewrite the checks those maps name.
Preserving the original maps would require another compiler interface,
which this generator does not add.

## Use captured layouts

The compiler's `cc-layouts FILE` command exposes the completed C layouts
without changing `cc-ir`, checked terms or assembly output. The generator
uses this command for manifests with `layouts = true`; libio enables it first.
A stdio batch enables it with `layouts = true` on the batch.
Each fixture receives a `<Name>Layout.v` beside its source tables.

The command prints `layouts(Records, Uses)` as a Prolog term. A record is
`record(Id, Names, def(Kind, Members, Size, Align), Fields)`. Its definition
comes directly from the completed type environment. Each field is
`field(Name, CType, Offset, Size, Align, Bits)`, using `member_layout/6`
and the member type's size and alignment. Flexible arrays have zero size.
Bit-fields retain their bit positions and widths in the Prolog output;
their byte size and alignment describe the declared type, not just the occupied bits.
Packed offsets and record alignments remain those of the completed definition.
Forward declarations use `incomplete` instead of a definition and have no fields.

The fixture tables omit record types that its functions do not use.
Selection starts with types in existing context records and follows record
member types, including pointer targets. The generator selects the fixture's
functions before merging layouts and rejects conflicting named layouts
from different translation units.

Named records keep their C names. Tags use names such as
`struct _IO_FILE`; anonymous typedefs use names such as `typedef _IO_lock_t`.
An unnamed record uses its object name, kind and translation-unit record ID.

Forward declarations without a complete definition have no layout table.
The `unavailable` list identifies their tags when no selected unit supplies a definition.

The Gallina `records` table gives each record's size and alignment. Its
`fields` table gives each tag, field, byte offset, type size and type alignment.
The `field_offset` lookup returns `None` for a missing entry.
`libio/FileInv.v` extracts its offsets, jump-table slots and stream-object
size from these entries during elaboration. Missing entries stop compilation.
The resulting definitions contain the same numerals as before, so existing
proofs still unfold them without evaluating a table lookup.
`libio/FileLayoutChecks.v` checks that the affine `off_ptr` formula agrees
with all twelve consecutive pointer fields. No soundness theorem takes a
generated layout table as a premise.

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

A function that is private to its unit is listed by its linked name,
`OBJECT#NAME`, such as `glibc_vfprintf_internal#__printf_buffer_putc`. In the
`string` and `formatter` layouts its Rocq constant is named after `NAME` alone,
here `glibc_printf_buffer_putc`. Its source tables are the module
`fn_OBJECT_NAME`, with every character that is not a letter, a digit or an
underscore changed to an underscore.

Existing fixtures must keep their names and presentation when units are added.
The `layout` setting chooses those conventions. The `mode` setting preserves
how each old driver compiled its units: `checked` by default, `trap` for stdlib
and `outcomes` for Len/Say.

Some linked units contain constructors that initialize the standard streams.
The `ctors` setting keeps those constructors. The stdio manifest uses a second
`[[batch]]` because its buffer fixtures come from a separate link.

The getopt and formatter fixtures store raw terms in slices. For HiAtexit and
the complete GNU Hello image, the generator runs the linked term through
`nanofil-model --gallina`. It builds the extracted driver through Nix on Linux.
Set `MODEL` to the path of a locally built driver on another platform.

The driver prints the functions returned by the Rocq decoder in SSA notation.
For example, a loop can branch to `poll "L10"`, and a zero-argument
indirect call can read `rawcall void %"fn"()`. A block lists its phis
after its label and its instructions before `=>`. In a proof session,
import `IRNotation` to see the same spelling when Rocq prints a function
or a block. Parentheses preserve an instruction that needs its full Gallina
spelling. For example, `store.ptr` requires the standard ordered pointer-store
effects. A different effect list prints in full. An outside function retains
its original transport term.

The smaller fixtures, including the program and spike examples, use
`cap_fn{` and `cap_blk{` from `CaptureNotation`. Their definitions still
have type `term`, and their existing witnesses check the result of decoding
that term. The printer's `--constructors` option emits the constructor
spelling for comparison.

The layout script groups
function definitions by the first two letters of their C symbol after removing
the unit qualifier, the glibc internal prefix and leading underscores. For
example, `HelloImageTypedIO` exports `hello_image_fn___GI__IO_wfile_overflow`.
A proof can import that family even if the function moves in the linked image.
The generated item lists reference the definitions in the original link order.
Hello checks the zero runs in each list and combines the proofs.

Rocq typechecks the printed AST. The quick Rocq check also compares the
printed module with in-kernel decoding of a fixture that exercises signed
loads, pointer effects, byte strings and outside functions.

Every function in a fixture row must be defined in its linked units. A missing
function fails generation and names the manifest row, rather than silently
emitting an empty decoded body. Run `test.sh CAPTURE` to check this rejection,
shared-prelude output, fixture corruption and the manifest proof-style switch.

## Select from a large linked image

GNU Hello linked with all the user glibc it reaches is too large to decode
within the compile budget. The `image` layout in `hello/code.toml` links that
whole image and keeps only the items that a proof needs. The manifest's
`objects` setting names a flake output whose `*.term` files are the program's
checked objects, and `object_prefix` is stripped from their names, as
`nix/hello-fixture.nix` does. The `units_files` setting names files of glibc
units to link before the manifest's own `units` rows. Hello's manifest names
`survey/glibc/run/units.txt` and `hello-siblings.txt`, the two files that
`nix/hello-glibc.nix` also reads, so both link the same 321 units. Generation
stops before compiling anything when a unit repeats or is missing from the
capture.

`image.pl` keeps each name in `FUNCTIONS` and the target of each kept alias,
with their terms and order unchanged. It stops generation when a name or a
target is missing, has more than one item, or is not a function or an alias.
The `compare` setting names another fixture, such as `intl/GettextLink`, and
each kept item must be the same term in that fixture's image. These checks run
on the whole image, which Rocq never sees. The generated file therefore states
them in a provenance section, with digests of the objects, the units and the
whole image. `test-image.py` checks these refusals on small images.

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
and `FILCC` set to the staging compiler. Pass the capture as a derivation
input. For either typed image, set `MODEL` to the executable from
`checks.x86_64-linux.nanofil-rocq.model.driver` to skip the driver's Nix
build. The Hello manifest also builds its captured program objects through Nix. The generator reads the canonical prelude from `rocq/glibc` and emits
shared-prelude fixtures by default. Use `--output TREE` to write a separate
tree, or `--update` to update the comparison tree.

The capture built successfully in an orb at
`/nix/store/7hh45cvwzrqyqvpknnlj82vrqdmg6kxw-filc-glibc-pp-2.44`.
The compiler came from Cachix; this capture was built locally, not substituted.
The check can therefore run in an orb and can be a dependency of the glibc
gate once its caller supplies the capture. It need not remain a manual check.
