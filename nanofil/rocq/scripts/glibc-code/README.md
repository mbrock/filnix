# The glibc code generator

The generator compiles the captured glibc units and links the checked IR.
It writes Rocq definitions of type `func` or `item` for each object that
supplies linked items. The proof fixtures assemble those definitions in link
order. Each directory's `code.toml` lists its units, roots and selected functions.

## Regenerate or check

Build the tools and capture from the repository root:

```sh
nix build -o /tmp/filcc .#filcc-staging
nix build -o /tmp/swipl --impure --expr \
  '(import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }).swi-prolog'
nix build -L -f nanofil/survey/glibc/capture.nix -o /tmp/glibc-pp
export FILCC=/tmp/filcc/bin/clang SWIPL=/tmp/swipl/bin/swipl
```

The default command checks the generated files and reports any changes,
missing files or stale files. Both write modes preserve the timestamps of files
whose bytes already match. An update also removes stale fixtures.

```sh
nanofil/rocq/glibc/code.sh /tmp/glibc-pp
nanofil/rocq/glibc/code.sh /tmp/glibc-pp --update
nanofil/rocq/glibc/code.sh /tmp/glibc-pp --output /tmp/generated-code
```

Use `--directory string` to select the views and source tables under
`gen/string`. This option can be repeated. Every run refreshes the shared
object inventory from all manifests because different links may reach
different definitions in the same object. Use `--directory glibc` to check or
write only the shared objects. Use `--tree` to choose the comparison or
update destination.

The generator uses `/tmp/glibc-pp` when no capture is supplied. It builds
`survey/glibc/capture.nix` if that directory is absent. It uses Python 3.11 or
newer, SWI-Prolog and the staging compiler. Set `MODEL` to an existing
`nanofil-model` executable to skip the Nix build for the extracted model.

## Image placement

The Hello manifest lists the symbols that wide-character conversion reads.
The generator runs the extracted loader’s placement and alias passes to write
their addresses and region ends to `HelloImagePlacement.v`. The conversion
proof imports that table and the C locale object that supplies the words.
`HelloWConvConsts.v` checks the addresses against the linked image, and
`HelloImageWConvObjs.v` proves that the loaded memory contains those words.

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
Compilation checks that every label a hint cites belongs to the captured
function, but it does not check that a name, path or location is accurate.

The generator writes four kinds of source hint, described in the sections
below. Source tables give locations, C names and loop headers. Names give
notations for temporaries. Block facts give liveness and memory footprints.
Layouts give the fields of C records.

## Use source tables

The generator also emits `<Name>Src.v` beside each code fixture.
Each sidecar imports the captured functions and groups its tables under
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
the fixture. The sidecar projects block labels straight from the typed function
definitions, so the VM does not compile the instruction bodies for this check.
Large fixtures put their tables in numbered source slices of about 100 KB.
Only the main sidecar imports the functions and checks membership.
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
nanofil/rocq/glibc/code.sh /tmp/glibc-pp --directory libio --output /tmp/generated-code
cp /tmp/generated-code/libio/*Src.v nanofil/rocq/glibc/gen/libio/
nanofil/rocq/glibc/code.sh /tmp/glibc-pp --directory libio
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

Compilation rejects labels that are not blocks of the captured function.
The shared `labels_valid` lemma performs this check once per fixture, using
the captured functions' block labels. The generator projects labels before compiling
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

## Add a unit or function

Each fixture row uses the following fields.

```text
NAME|ROOTS|UNITS|FUNCTIONS[|PROGRAM]
```

An empty roots or units field inherits the manifest's setting. The linker
keeps items reachable from the roots and preserves object and item order.
It scopes private symbols to the input object, so a function such as
`__printf_buffer_putc` in vfprintf is named
`glibc_vfprintf_internal#__printf_buffer_putc` in the linked IR.
`FUNCTIONS` lists exact linked names for the source tables. The libio and
stdio selections also limit their module lists to those functions. An absent
function fails generation. `PROGRAM` names a C source relative to `nanofil`.

The linker reports the object supplying each item after reachability and
weak-symbol resolution. The extracted model reads the linked term and
prints the typed Gallina. The generator groups glibc definitions under
`gen/glibc` by the full capture path and rejects different bodies for the
same object and symbol. Program directories hold their own objects and
join lists for their images. The list references preserve aliases,
initializers and link order.

Import the generated object to use its function or data in a proof. For
example, `Unit_string_strlen_os.fn___strlen` names the body in
`string/strlen.os`. You can also import `IRNotation` to use the same SSA
spelling when Rocq prints a function or block. A pointer store with unusual
effects keeps its full Gallina form. An outside function retains its
transport term. The quick Rocq check compares the resulting typed module
with decoding on a small fixture that exercises these cases.

## Select from a linked image

Hello's manifest selects the functions and aliases used by the gettext
and strchr proofs. The `objects` setting supplies the program's checked
objects. The `units_files` setting supplies glibc units ahead of the
explicit `units` rows. Generation fails before compiling a linked image
if one of its units is missing or repeated.

The selection keeps each requested name and each retained alias's target
in link order. The `compare` setting names a standalone fixture whose
matching items must have identical terms. Both views use the canonical
definitions. The provenance records the input digests and that comparison.
The complete Hello image also checks its initializer zero runs in Rocq.

## Start a block lemma

`skeleton.py` links one manifest fixture and prints statement skeletons for
every block of a named function. The unit argument names a directory and a
fixture row, not a captured translation unit. The function argument uses its
exact linked symbol, including the object prefix of a private function:

```sh
python3 -I nanofil/rocq/scripts/glibc-code/skeleton.py \
  getopt/Getopt 'glibc_getopt#process_long_option' \
  --capture /tmp/glibc-pp --rocq-function "Unit_posix_getopt_os.fn_glibc_getopt'23process_long_option"
python3 -I nanofil/rocq/scripts/glibc-code/skeleton.py \
  hi_atexit/HiAtexit __GI__IO_puts \
  --capture /tmp/glibc-pp --rocq-function Unit_libio_ioputs_os.fn___GI__IO_puts --expr-type sexpr
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
backedges and phi operands on their particular incoming edges. The analysis follows control-flow edges between blocks.

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
