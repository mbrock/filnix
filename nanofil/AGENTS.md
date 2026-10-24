# nanofil

A C compiler in Prolog that emits Fil-C ABI assembly. Read
[PLAN.md](PLAN.md) for milestones and decisions, then the `docs/mN.md`
for the area you touch. ABI facts are in
[docs/abi-findings.md](docs/abi-findings.md); add to it when you verify
something new against the pinned sources.

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
nanofil/tests/snapshot.sh [REV]                # every output identical to REV's (default HEAD)
nix build .#checks.x86_64-linux.nanofil        # everything; must pass before pushing
nix build .#checks.x86_64-linux.nanofil-hello  # GNU hello built only by nanofil, vs filcc
nix build .#checks.x86_64-linux.nanofil-zlib   # zlib built only by nanofil, vs filcc
nix build .#checks.x86_64-linux.nanofil-lua    # Lua built only by nanofil, vs filcc
```

`bin/nanofil` runs on SWI-Prolog by default; `NANOFIL_HOST=trealla` (with
`TPL=/tmp/tpl-native/bin/tpl`) runs the same commands on Trealla. Under
SWI, `swipl ... -g 'profile(Goal)'` shows where time goes.

- Run Prolog with stdin closed (`</dev/null`).
- Show that a new test can fail: plant the bug it targets, watch it fail,
  restore. Say so in the commit or report.
- Code must run on both hosts. Write Trealla's dialect (double_quotes
  chars, `library(dcgs)`, `format_//2`, character-list `phrase_from_file`);
  `src/swi/` maps it onto SWI. Avoid `char_type/2` (the hosts' classes
  differ) and `phrase/2,3` over non-list state (SWI requires a list).
  To thread a state through a DCG, wrap it in a one-element list and use
  semicontext, `state(S), [S] --> [S].` and `state(S0, S), [S] --> [S0].`,
  with `phrase(G, [S0], [S])` (c_lower.pl, promote.pl).
- The Trealla DCG translator rejects an if-then chain without a final
  else inside `-->` bodies; end chains with `; []`.
- On Trealla a 200-function `gen.py` corpus takes GBs of RAM; run one at
  a time there.
- On Trealla, a DCG that tries alternatives which share a prefix over a
  char list from `atom_chars/2` returned a wrong first solution after
  the interpreter had run (October 2026; a literal list was fine). To
  look a name up in a relation, generate the candidates' chars and
  compare.

## The refactoring campaign

nanofil is being refactored toward a specification that compiles
programs: each fact about C, the IR or Fil-C stated once, as a relation
everything else reads. [docs/campaign.md](docs/campaign.md) holds the
ambition, the working rules (snapshot byte-identity, fail-first tests
for behaviour changes) and the ordered roadmap; read it before
refactoring, and mark roadmap steps done when they land.
[docs/factorings.md](docs/factorings.md) logs what has been done.

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

## Working alongside other threads

Several threads may work on nanofil at once, each owning one workstream.

- Stay inside the files your task names. Shared files (`ir.pl`,
  `interp.pl`, `filc_amd64.pl`, `c_lower.pl`, `nix/check.nix`) change
  only for what your task needs; keep those edits small and say which
  you touched.
- The IR term grammar in `ir.pl` is the contract between the frontend,
  interpreter and backends. Changing it needs the orchestrating thread's
  agreement first.
- Commit to main and push with `scripts/ship` when the Nix check passes
  (root AGENTS.md). From an orb it rebases and pushes without publishing;
  nanofil changes leave every CI output cached, so CI stays green. If the
  rebase conflicts in a shared file, resolve it keeping both sides'
  intent and rerun the check.
- Nothing under nanofil should change the toolchain. If the pre-push hook
  says "CI will fail until these are published", stop, do not push with
  --no-verify, and report what changed it.
- Report back with what changed, the evidence (commands and decisive
  output), and anything you decided that others should know.
