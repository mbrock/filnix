# Workbench IR samples

All IR samples use `play_view:ir_module//3`, `play/ir.js`, and `play.css`,
exactly like the playground. `samples.pl` keeps the older metadata-free
compiler sample to exercise the raw-identity fallback.

`sum-o0.ir` and `sum-o1.ir` are **actual compiler output**, not handwritten
metadata. They retain only `sum` and its accompanying context from the
playground's `sum.c`. Regenerate from this directory (the filter changes
only term selection and whitespace, never the records):

```bash
set -o pipefail
export SWIPL=/tmp/swipl/bin/swipl FILCC=/tmp/filcc/bin/clang
select_sum() {
  "$SWIPL" -q -g 'repeat, read(T), (T == end_of_file -> ! ; ((T = func(sum,_,_,_,_) ; T = context(sum,_)) -> write_term(T,[quoted(true),fullstop(true),nl(true)]) ; true), fail)' -t halt
}
../../bin/nanofil cc-ir ../play/examples/sum.c </dev/null | select_sum > sum-o0.ir
../../bin/nanofil -O cc-ir ../play/examples/sum.c </dev/null | select_sum > sum-o1.ir
```

Render the workbench from this directory (the output directory must exist):

```sh
$SWIPL workbench.pl /tmp/nanofil-workbench ../../src </dev/null
```

UI contract tests, from the repository root:

```sh
/tmp/swipl/bin/swipl -q -s nanofil/web/play/view_tests.pl -g run_tests -t halt </dev/null
node --test nanofil/web/play/ir.test.mjs
node --check nanofil/web/play/ir.js
node --check nanofil/web/play/play.js
node --check nanofil/web/workbench/samples.js
```

Pretty serials are zero-based, per source spelling and role, allocated in
the sidecar's historical value-record order (with alias-only old values
also reserved). Displaced `history/5` entries reserve serials by their
metadata identity, never by the reused raw temporary. Passes must retain
this order and append new records.
Removing a definition must not renumber the remaining values. Shadowed
bindings get a separate superscript scope qualifier; `data-binding` and
`data-tmp` retain their compiler identities. An alias never renames its
replacement. Unnamed numeric identities also use real subscripts
(`v12`, `chk3`, `pr.2`); arbitrary nonnumeric identities remain verbatim.
Tooltips distinguish the **IR machine class**, the originating **C
expression type**, and the **C binding type**. A low-level intermediate
need not have the type of the C expression it originated in.

Source hints are sparse enclosing-statement lines, not expression spans.
Each site's origins must resolve to exactly one file/line before it gets
`data-line`. An origin's own location takes precedence over its parents;
generated origins with no location inherit their parents. Merged or
unresolved locations deliberately have no single-line navigation. Legacy
`loc` input still renders, but cannot override an ambiguous sidecar site.
