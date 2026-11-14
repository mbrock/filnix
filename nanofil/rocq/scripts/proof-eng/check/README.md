# Checks before the proof-engineering cutover

These commands compare compiled statements and campaign assumptions, then run
the local checks from the glibc, docs, and site workflows. They do not publish
anything. A missing object or failed query is a failure, not an unchanged statement.

## Run the complete check

Merge the latest main into the pipeline branch first. From the repository root,
run `bash nanofil/rocq/scripts/proof-eng/check/run.sh /tmp/proof-cutover` with a
new output directory. The command fetches main, records both revisions, applies
the current pipeline to main's glibc sources, and makes a materialized worktree.
It builds both proof trees and prints a verdict for each check. It checks main
again at the end and fails if main advanced during the run.

Before rewriting the tree, it runs stage 10's duplicate-name check on a copy
and saves `flatten-names.json` in the packet. The check rejects a new name that
several files export if any file uses that name without a module prefix.
The compiled-statement check still runs separately.

`PE_JOBS` controls compilation concurrency and defaults to eight.
`PE_QUERY_JOBS` controls statement queries and defaults to two. The original
Hello audit can consume substantial memory, so campaign audits run sequentially.
The output directory retains logs, reports, sources, and objects. An explicit
second argument selects a historical baseline for diagnosis; such a run cannot
return a successful cutover verdict.

Only the exit statuses of these local commands count. The hosted docs and Rocq
workflows can report success after a failed Nix build because their logging
pipelines do not enable `pipefail`.

The commands from the workflows are:

| Part | Local command in the materialized worktree |
| --- | --- |
| Foundation cache | `python3 scripts/ci-cache-check.py packages.x86_64-linux.filcc-staging packages.x86_64-linux.site-swipl` |
| Glibc | `nix build -L --no-link --keep-going .#checks.x86_64-linux.nanofil-glibc` |
| Glibc patch regressions | `nix build -L --no-link -f nanofil/survey/glibc/regress.nix units` |
| Docs | `nix build -L --no-link .#checks.x86_64-linux.nanofil-docs` |
| Site | `nix build -L --no-link .#site` |
| Site serving contracts | `node --test deploy/site/worker.test.mjs` |
| Site Python tests | `python3 -m unittest discover -s tests -p 'test_site_*.py'` |

The glibc derivation compiles every file, compiles every strict parser reprint,
checks dependency declarations, and runs native syscall-contract probes. The
docs derivation tests rendering, checks document and concept references, and
checks the guide's generated outputs. The site build renders the proof sources
without requiring every proof to compile. Publication, cache uploads, and live
release checks are deliberately excluded.

## Compare statements without rebuilding everything

Source `nanofil/rocq/scripts/proof-eng/env.sh`, then build the printer plugin:

```sh
bash nanofil/rocq/scripts/proof-eng/check/plugin.sh /tmp/check-tools/plugin
python3 nanofil/rocq/scripts/proof-eng/check/check.py statements BEFORE AFTER \
  --abstract-after ABSTRACT_AFTER --plugin /tmp/check-tools/plugin --output /tmp/statement-report
```

Both trees must contain their compiled `.vo` and `.glob` files. The checker
rejects `.glob` files whose source digest is stale. `--files GlibcLogic.v`
restricts a diagnostic run; the full command never restricts coverage.

The full command builds a second candidate with `PE_RUNTIME=abstract`. It uses
`rocq dep` on the original tree to find every file that names `InterpRuntime`
or depends on a file that does. Those files are compared against the concrete
candidate, with the original functor instantiated at `InterpRuntime`. Every
other original file must compile and compare against the abstract candidate.
The report retains the dependency output, the file partition, and declaration
counts for each runtime. Compilation success never chooses a file's runtime.
`check.py partition ORIGINAL --output DIRECTORY` exports that same partition
and a `general-targets.txt` file. The full command passes those original general
targets to stage 50 through `PE_PROGRAM_TARGETS`, so the abstract conversion
covers their complete dependency closure without rebuilding concrete entrypoints.

The source selects lemmas, theorems, corollaries, and definitions explicitly
returning `Prop`. Rocq's `.glob` supplies their module scopes. Each probe
instantiates a functor over an abstract runtime and its logic, then asks Rocq
for the elaborated type with implicit arguments, notations, and universes
exposed. Explicit proposition definitions also have their bodies printed.
The report retains module parameters. Abstract runtime references and concrete
`InterpRuntime` references remain distinct in the comparison.

The printer plugin uses Rocq's canonical global references and absolute names.
Printing depth and width are both set to one million; an ellipsis fails the
export instead of silently equating truncated types. Hidden implementation
lemmas in sealed modules are queried in a temporary source copy before sealing,
after their sections have generalized the hypotheses.
The Python comparison resolves known module aliases but never strips arbitrary
qualifiers. Thus two imported definitions with the same short name remain
different, even if the statement's source text is identical. Unknown aliases
remain qualified. Differences in unresolved paths or universe names can require
review; this is a conservative comparison, not a decision procedure for logical
equivalence. A changed statement is never automatically allowlisted. Removed
wrappers come from the file's module declarations. Included members come from
compiled export records. A signature parameter can refer to a flat file only
when its concrete definitions come from that file through an `Include` or a
signature-checked implementation. Opaque signature parameters stay distinct.

`report.json` retains raw and normalized statements, module parameters, and
errors. `report.txt` lists each changed, added, or removed statement with its
file, name, and both normalized statements. Missing or stale objects in the
selected trees fail the overall check, even when other files compare equal.

For generation, `--discovery` treats the expectation file as a candidate list:
unchanged candidates do not produce "expected change was not observed" errors.
Every discovered difference remains unaccepted, even if a matching pin exists.
Compiler, probe, and inventory errors still fail. This mode gathers evidence;
the ordinary comparison and packet checks decide acceptance.

## Reproduce and compare the campaign audits

We audit Hello twice because its concrete and abstract runtimes expose different
assumptions. The concrete proof must print "Closed under the global context".
The abstract proof must retain its original statement and twelve assumptions,
including their types. `audit-contracts.json` records the permitted assumptions
for every query; an empty list requires Closed. The statement comparison uses
the original dependency graph to choose which runtime to compare.

`layouts/original/` contains the lead's original query files, including the
regression proofs and count-wrap controls inside those queries. A layout is data:
replace imports and module applications in a separate directory when the proof
layout changes, while retaining the query targets and their contracts.
An optional `assumption-aliases.json` in that directory maps exact module prefixes,
such as `Fix.R` to `AuditRuntime`. The audit comparison checks every assumption's
full printed type after those explicit renamings, not just the twelve names.
It also compares each audited statement using the qualified printer and the
statement checker's module resolver. Changed statements fail unless they meet
the exact stage-50 permission described below, even when their proofs are Closed.

```sh
python3 nanofil/rocq/scripts/proof-eng/check/audit.py BEFORE \
  --output /tmp/audit-before
bash nanofil/rocq/scripts/proof-eng/check/prepare-layout.sh BEFORE /tmp/flat-layout
python3 nanofil/rocq/scripts/proof-eng/check/audit.py AFTER \
  --layout /tmp/flat-layout --output /tmp/audit-after
bash nanofil/rocq/scripts/proof-eng/check/hello-abstract.sh BEFORE /tmp/hello-abstract
python3 nanofil/rocq/scripts/proof-eng/check/compare-audits.py \
  /tmp/audit-before/report.json /tmp/audit-after/report.json \
  --hello-abstract /tmp/hello-abstract/audit/report.json
```

The layout generator applies the pipeline to copies of the original queries.
Those generated queries are a starting point, not an assertion that the new
layout supports the audit. A failed query prevents a passing verdict. Set
`PE_AUDIT_LAYOUT` for the complete command to use a reviewed layout instead.
The generated concrete layout supplies `contracts.json` with Hello's Closed
expectation. `hello-abstract.sh` builds only Hello's dependency closure and uses
the original twelve-assumption contract. A typeclass design needs a separately
reviewed contract; these checks do not anticipate that decision.

## Review intentional statement changes

Each file in `expected-statement-changes/` uses action rows separated by tabs:

```text
changed	file.v	name
added	file.v	name
removed	file.v	name
moved	oldfile.v	old_name	newfile.v	new_name
```

Lines starting with `#` hold rationale and stage-specific source guards. The
checker rewrites only the exact full references named by move rows and still
compares each moved declaration's type and proposition body. Several sources
may move to one destination only when every source is listed, present, and
equal to the destination. The declaration's universe names move with it.
Proof aliases are compared by type rather than by proof body. An unchanged
move can pass without a statement exemption. Other changes require an exact pair of
elaborated statements in the companion `.elaborated.json` file. The report prints
every accepted change and both types. Audited endpoints cannot be exempted.

To capture a stage's review material, compile its immediate before and after
trees, then run the checker restricted to the manifest's files. Replace
`20-keeps` with the stage's name where appropriate:

```sh
check=nanofil/rocq/scripts/proof-eng/check
manifest=$check/expected-statement-changes/20-keeps.txt
python3 "$check/check.py" statements BEFORE AFTER --plugin /tmp/check-tools/plugin \
  --expectations "$manifest" --output /tmp/stage-statements \
  --files $(python3 "$check/expectations.py" files "$manifest")
python3 "$check/expectations.py" export "$manifest" /tmp/stage-statements/report.json
```

The first command fails until the differences are approved. The export refuses
missing queries or unlisted differences. Review the exported before/after
statements before committing the JSON. Repeating the check then accepts those
exact pairs but rejects an additional alteration to an already listed lemma.
Use `export --append` to retain an independently elaborated runtime variant
without replacing the existing pair. Both pairs remain explicit in the packet;
the comparison does not substitute one runtime for another.
Each intentional stage also supplies a `.equivalence.v` proof for the cutover
packet; the declaration list alone does not establish equivalence.

Stage 30 instead supplies unchanged-statement evidence. `tactics-boundary.sh`
creates its complete before and after trees from the original sources. Build
both, then pass `--stage30-before BEFORE --stage30-after AFTER --plugin PLUGIN`
to `packet.py`. The packet compares every declaration across that boundary,
requires all eight reviewed sources to equal their five targets including
universes, checks the added rule against its pinned type and audits it Closed,
and runs `lint-tactics.py --max 226`. No equivalence lemma is required for this
statement-preserving stage. `run.sh` prepares and checks these trees itself.

`python3 check/packet.py POST_TREE --output cutover-packet.md`, run from the
pipeline directory, assembles the three files into one document. It checks that
the elaborated pairs name exactly the manifest's declarations, compiles the
equivalence file, and independently audits every lemma in it as Closed. It also
runs `python3 stages/STAGE.py --check POST_TREE` to connect the equivalences to
the stage's source guards. Missing files, extra declarations, open proofs, and
failed stage validation prevent a passing packet. `run.sh` appends its revisions,
local gate verdicts, and complete statement differences to this packet.

Stage 50 generates its three evidence files under `POST_TREE.program/` rather
than committing them. The packet invokes `50-program.py --check POST_TREE`
first, then reads those files. That command validates the reviewed action list
and source guards, regenerates the evidence, and compiles and audits adapters
in bounded shards. The packet does not repeat the monolithic compilation.

`audit-changes.json` identifies exactly forty intermediate declarations by file
and name. It retains their reviewed old types, implementation names, and adapter
names from `c6c7ea2`. A generated baseline cannot replace those old types. Each
accepted change requires an exact elaborated pair and both checked adapters;
a name on the list alone grants no permission. Audit reports also record the
resolved declaration identity and the tree's source digest. The new declaration
must retain the old declaration's assumption names and types.

The interpreter adapters must print Closed. Abstract adapters may use only
qualified fields of the declared `Glibc.Fix.R` module. The old and new statements
must list identical assumption names and types, and each adapter's assumptions
must be a subset of that set with the same types. The same declaration must
also have Closed interpreter adapters. Reports label this evidence
"abstract: runtime fields only" and give each pair's field count, not "Closed".
Equivalence source cannot introduce axioms, parameters, admitted proofs, or a
declared module. Endpoint protection and Hello's twelve-assumption contract
remain unchanged.

A successful stage-50 packet writes `OUTPUT.stage50.json` beside its Markdown
report. This local receipt binds the generated evidence, reviewed action list,
reviewed old types, and tree sources by hashes. Both `check.py` and
`compare-audits.py` accept `--stage50-evidence RECEIPT`; repeat it for the two
runtimes. Missing or stale evidence fails. `packet.py --stage50-only` checks
the additional abstract boundary without repeating the other stages. Pass its
Closed counterpart with `--interpreter-evidence CONCRETE_RECEIPT`.

## Test that the checks reject mutations

After sourcing the environment and building the plugin, run:

```sh
PE_CHECK_PLUGIN=/tmp/check-tools/plugin \
  python3 nanofil/rocq/scripts/proof-eng/check/test_check.py
```

The test compiles disposable libraries with real Rocq. It accepts changed
comments and rejects a changed proposition, an import-order binding change,
a runtime specialization, and a proof that depends on an injected axiom.
