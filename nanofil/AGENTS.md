# nanofil

A C compiler in Prolog that emits Fil-C ABI assembly. Start with
[docs/guide.md](docs/guide.md): one C function through every stage, a
map of the modules, the concepts and where to start a change. Read
[PLAN.md](PLAN.md) for milestones and decisions, then the `docs/mN.md`
for the area you touch. ABI facts are in
[docs/abi-findings.md](docs/abi-findings.md); add to it when you verify
something new against the pinned sources. What Fil-C does with C's
undefined behaviour (overflow, shifts, aliasing, uninitialized reads)
is in [docs/ub.md](docs/ub.md).

## Tools

Build these once per orb (all cached):

```sh
nix build -o /tmp/filcc .#filcc-staging                          # /tmp/filcc/bin/clang
nix build -o /tmp/swipl --impure --expr \
  '(import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }).swi-prolog'
nix build -o /tmp/tpl-native --impure --expr \
  'import ./nanofil/nix/trealla.nix { pkgs = import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }; }'
nix build -o /tmp/filc-ref .#lib.x86_64-linux.filc-staging-ref-src # staging docs, pass, runtime
```

Nanofil requires staging Fil-C 0.687; there is no 0.686 ABI compatibility.
Use `filc-staging-ref-src` to look up how Fil-C behaves. Do not fetch `filc0-src`
(all of LLVM and clang) unless you are building the compiler.

## Tests

```sh
export SWIPL=/tmp/swipl/bin/swipl FILCC=/tmp/filcc/bin/clang
(cd nanofil/src && ../bin/nanofil --script ../tests/unit.pl </dev/null)
(cd nanofil/src && ../bin/nanofil cc-ir ../tests/c/basic.c </dev/null)
nanofil/tests/difftest.sh FILE.ir|FILE.c...    # interpreter vs native (and clang for .c)
nanofil/tests/progtest.sh                      # whole programs vs filcc
nanofil/tests/reject.sh                        # unsupported C is refused
nanofil/tests/arith.sh slice|complete|random SEED COUNT DEPTH  # const_eval vs IR vs clang (docs/arith.md)
nanofil/tests/snapshot.sh [REV]                # every output identical to REV's (default HEAD)
nanofil/tests/guide.sh [--check]               # regenerate (or check) the outputs in docs/guide.md and README.md
swipl nanofil/tests/docs.pl -- nanofil/src     # every module has a header and every export PlDoc
(cd nanofil && swipl web/dterm.pl --check docs/guide.md docs/formal.md docs/filc.md docs/iris.md src --concepts=docs/concepts --rocq=rocq/theories)  # the documents', concepts' and [[concept]] references resolve
(cd nanofil/src && ../bin/nanofil --script ../tests/gen.pl SEED COUNT </dev/null) >gen.ir  # random IR corpus
nix build .#checks.x86_64-linux.nanofil        # everything, in one build (about 45 min); CI runs it in 8 shards after each push
nix build .#checks.x86_64-linux.nanofil-rocq   # quick: model, parse.sh, small corpus; base verdicts only
nix build .#checks.x86_64-linux.nanofil-rocq-full # deliberate full mutation campaign (docs/rocq.md)
nix build .#checks.x86_64-linux.nanofil-hello  # GNU hello built only by nanofil, vs filcc
nix build .#checks.x86_64-linux.nanofil-zlib   # zlib built only by nanofil, vs filcc
nix build .#checks.x86_64-linux.nanofil-lua    # Lua built only by nanofil, vs filcc
nix build .#checks.x86_64-linux.nanofil-bzip2  # bzip2 built only by nanofil, vs filcc
nix build --impure -f nanofil/bench -o nanofil/bench/out && (cd nanofil/bench && python3 run.py)  # speed vs filcc -O2 (docs/perf.md)
```

All the Nix checks at once: `scripts/nanofil-checks` (or name some) builds
them in one `nix build --keep-going` and prints pass/FAIL per check. On
swa that spreads them over swa and its remote builders (igloo, chapel;
`/etc/nix/machines`), which an orb cannot reach. The ports survey
(docs/survey.md) is the same: run it on swa. An orb thread that needs the
full set or a survey rerun after a push asks the orchestrating thread, or
a thread on runner swa, to run it at the pushed commit.

Before pushing, run what covers your change: unit tests, the difftests or
programs you touched, `snapshot.sh` for output changes, `nix build
.#checks.x86_64-linux.nanofil-rocq` (1–2 minutes) for model, compiler or
validator changes, and a package check for frontend or backend changes.
Then push with `scripts/ship` (nanofil-only pushes skip the cache gate)
and keep working. After the push, CI runs `checks.nanofil` split into 8
shards (.github/workflows/nanofil.yml), quick Rocq and the site. If one
of your runs goes red, fix it forward. To see the whole check on a
branch before pushing, run the Nanofil workflow on it with
`workflow_dispatch`, or build one shard locally:
`nix build -L --impure --expr '(builtins.getFlake (toString ./.)).lib.x86_64-linux.nanofil-check { shard = "3/8"; }'`.
Steps live in `nix/check.nix`'s `steps` function; give each a unique
label, since labels select a step's shard, and refresh
`tests/check-times.tsv` from a run's step timings when the split drifts.

## Visible progress

`tests/watch.py --label LABEL -- COMMAND...` runs a check with UTC
timestamps, elapsed time and its latest output every 15 seconds, warns
at a soft budget (60 s by default) and kills the process group at a hard
deadline (300 s by default, exit 124). Main-check steps and
`tests/par.sh` files use it. Run long experiments through it too, so
whoever is watching sees the active step rather than silence. A step
that keeps warning is worth splitting, caching or speeding up; do not
delete its cases to make it fast.

File runners default to at most four concurrent files and print their
fanout. Program and corpus modes are four disjoint groups; all cases and
modes remain covered. Compile failures retain source, mode, status, command,
stderr and wall/CPU timings. Measure contention before raising fanout.
The site caches Prolog rendering, Rocq rendering and proof capture
separately, retaining the complete cross-file index and actual states.

## Local iteration

For many runs, `bin/nanofil --save-state /tmp/nanofil.state` and
`export NANOFIL_STATE=/tmp/nanofil.state` skip compiling `src/` each time
(0.26 s to 0.05 s); rebuild the state after editing `src/`, or unset it.

`bin/nanofil` runs on SWI-Prolog by default; `NANOFIL_HOST=trealla` (with
`TPL=/tmp/tpl-native/bin/tpl`) runs the same commands on Trealla. Under
SWI, `swipl ... -g 'profile(Goal)'` shows where time goes.

- Run Prolog with stdin closed (`</dev/null`).
- Show that a new test can fail: plant the bug it targets, watch it fail,
  restore. Say so in the commit or report.
- Trealla is paused (October 2026): develop, test and measure on SWI
  only, and don't spend time on Trealla failures or memory. The Nix
  check runs Trealla only with `withTrealla = true` (nix/check.nix). The
  dialect rules below still hold, so the way back stays cheap.
- Scryer was tried in October 2026 and is not worth supporting yet
  ([docs/hosts.md](docs/hosts.md)). Write strict ISO syntax anyway: bracket
  an operator atom used as an operand, `Op == (=)`, not `Op == '='`.
- Code is written to run on both hosts. Write Trealla's dialect (double_quotes
  chars, `library(dcgs)`, `format_//2`, character-list `phrase_from_file`);
  `src/swi/` maps it onto SWI. Avoid `char_type/2` (the hosts' classes
  differ) and `phrase/2,3` over non-list state (SWI requires a list).
  To thread a state through a DCG, wrap it in a one-element list and use
  semicontext, `state(S), [S] --> [S].` and `state(S0, S), [S] --> [S0].`,
  with `phrase(G, [S0], [S])` (c_lower.pl, promote.pl).
- The Trealla DCG translator rejects an if-then chain without a final
  else inside `-->` bodies; end chains with `; []`.
- On Trealla a difftest of a 200-function `gen.pl` corpus takes GBs of
  RAM; run one at a time there.
- On Trealla, a DCG that tries alternatives which share a prefix over a
  char list from `atom_chars/2` returned a wrong first solution after
  the interpreter had run (October 2026; a literal list was fine). To
  look a name up in a relation, generate the candidates' chars and
  compare.

## The semantic foundation and campaign

nanofil is a working compiler and an executable account of capability
semantics. [docs/campaign.md](docs/campaign.md) states its foundation and
current priorities; read it before semantic or structural work.
[docs/formal.md](docs/formal.md) is the formal campaign built on it:
a Rocq model of the checked IR, the runtime as axioms, and certificates
that discharge checks; work in it follows that page's working method.
[PLAN.md](PLAN.md) tracks milestones and [docs/factorings.md](docs/factorings.md)
records completed refactorings. The old frontend roadmap is a record,
not a request to repeat completed work.

- Separate safety requirements, evidence that discharges them, and their
  implementation. Checked IR accepts adjacent checks and, since M7's
  first slice, forward reuse of heap check evidence by later scalar
  accesses (docs/m7.md); other new evidence needs a reviewed
  validator/interpreter/emitter contract.
- State the abstract facts, transfer/merge rules and invalidating effects
  of an analysis. Keep passes independently callable as ordinary Prolog
  relations; do not require microscopic passes or wrapper frameworks.
- Distinguish checked-IR safety, behavior preservation and native/runtime
  correctness. Shared relations, bounded searches, tests and `doc/3`
  examples are not a universal proof. Preserve current trap behavior
  unless a changed observation contract is explicitly reviewed.
- AI may propose transformations, invariants or proofs; acceptance must
  check the result under fixed assumptions, not trust the proposer.
  Unsupported evidence or exhausted search never authorizes check removal.
- Keep the selectable reference path and the existing snapshot/fail-first
  gates. The playground must show actual compiler products, not a second
  implementation of their explanation. General arithmetic optimization
  and register allocation are not prerequisites for semantic work.

## Purity where it pays

The style follows Triska's [The Power of Prolog](https://www.metalevel.at/prolog)
(PLAN.md's rules, docs/handoff.md): relation names, clean
representations, case analysis in clause heads, DCG semicontext for
state. Two of its tools do not pay in compiler code on ground data,
measured in October 2026:

- `#=` instead of `is/2` throughout: +10% on SWI, but 4-9x the time and
  up to 14 GB instead of 3 GB on Trealla (c-testsuite 00200 and 00040,
  `-O cc`). CLP(Z) stays in `interp.pl`, which must run backwards.
- `if_/3`: 18x (SWI) and 7x (Trealla) the cost of `->` per dispatch,
  and SWI has no `library(reif)`. Clause heads with first-argument
  indexing cost the same as `->` on Trealla and are pure.

## Documentation is a relation

A module listed in `tests/unit.pl`'s `documented_module/1` (so far
`c_types`) states its documentation as `doc/3` facts, one just before
each predicate: head with modes, determinism, and a list of argument
descriptions, prose strings, `cites/1` and examples
([docs/dterm.md](docs/dterm.md)). The examples are tests:
`doc_examples` in `tests/unit.pl` runs them on both hosts, and the wiki
pages run them again and mark each ✓ or ✗.

- A new or changed predicate in such a module gets a `doc/3` fact. Give
  an example per case of its behaviour: both sides of a boundary, the
  failing case (`fails/1`), and asymmetric inputs where arguments could
  be confused.
- Derive expected values from the standard or by hand, never by running
  the code.
- Cite the paragraph a rule implements (`cites('C11 6.3.1.8p1')`).
- Write `?(X)`, not `?X`, and one string per line of prose; a
  `doc/3` fact replaces the `%!` comment, it does not repeat it.
- Snapshot byte-identity is unaffected: `doc/3` is never called by the
  compiler.
- A file's header comment is its page's lede, written in the little
  Markdown dterm reads ([docs/dterm.md](docs/dterm.md)): `##` headings,
  pipe tables for term forms and their meanings, term forms in
  backticks as valid Prolog so they draw as terms, and a ```` ```diagram ````
  only where a picture helps. `c_types.pl`'s header is the model.
- Every other module documents each export with a PlDoc comment just
  above its first clause: `%! name(+In, -Out) is det.`, a blank `%`
  line, then prose saying what it means. `tests/docs.pl` fails the
  check when a module lacks a header or an export lacks its doc
  ([docs/guide.md](docs/guide.md), Conventions).

## Concepts

A term a reader may not know (a capability, a renew, a doomed frame)
is explained once, in [docs/concepts/ID.md](docs/concepts/), and linked
from Prolog comments, Rocq `(** *)` comments and documents with
`[[name]]` or `[[name|text]]`; a line `![[name]]` draws it in place
([docs/dterm.md](docs/dterm.md), Concept nodes). Link a concept rather
than explaining it again in a module header or a `.v` file, and add one
when a term needs explaining in more than one place. In the Rocq, give
each definition, lemma and theorem a short `(** *)` doc in plain words
just before it, with `[name]` for the Rocq names it uses.

## Working alongside other threads

Several threads may work on nanofil at once, each owning one workstream.

- Stay inside the files your task names. Shared files (`ir.pl`,
  `interp.pl`, `filc_amd64.pl`, `c_lower.pl`, `nix/check.nix`) change
  only for what your task needs; keep those edits small and say which
  you touched.
- The IR term grammar in `ir.pl` is the contract between the frontend,
  interpreter and backends. Changing it needs the orchestrating thread's
  agreement first.
- Push your own work to main with `scripts/ship` when it is coherent
  and its targeted checks pass; there is no lander or receipt. Commit
  small and push often, so others rebase onto your work early. If
  `scripts/ship` stops on a rebase conflict, resolve it preserving both
  sides' intent and run it again.
- Nothing under nanofil should change the toolchain. If the pre-push hook
  says "CI will fail until these are published", stop, do not push with
  --no-verify, and report what changed it.
- Report back with what changed, the evidence (commands and decisive
  output), and anything you decided that others should know.
