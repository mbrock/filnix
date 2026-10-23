# nanofil

A C compiler in Prolog that emits Fil-C ABI assembly. Read
[PLAN.md](PLAN.md) for milestones and decisions, then the `docs/mN.md`
for the area you touch. ABI facts are in
[docs/abi-findings.md](docs/abi-findings.md); add to it when you verify
something new against the pinned sources.

## Tools

Build these once per orb (all cached):

```sh
nix build -o /tmp/filcc .#filcc                                  # /tmp/filcc/bin/clang
nix build -o /tmp/tpl-native --impure --expr \
  'import ./nanofil/nix/trealla.nix { pkgs = import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }; }'
nix build -o /tmp/qbe-p --impure --expr \
  'import ./nanofil/nix/qbe.nix { pkgs = import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }; }'
nix build -o /tmp/filc-ref .#lib.x86_64-linux.filc-ref-src       # Fil-C docs, pass, runtime (6.5 MB)
```

Use `filc-ref-src` to look up how Fil-C behaves. Do not fetch `filc0-src`
(all of LLVM and clang) unless you are building the compiler.

## Tests

```sh
export TPL=/tmp/tpl-native/bin/tpl QBE=/tmp/qbe-p/bin/qbe FILCC=/tmp/filcc/bin/clang
(cd nanofil/src && $TPL -q ../tests/unit.pl </dev/null)
nanofil/tests/difftest.sh FILE.ssa|FILE.c...   # interpreter vs native (and clang for .c)
nanofil/tests/progtest.sh                      # whole programs vs filcc
nanofil/tests/reject.sh                        # unsupported C is refused
nix build .#checks.x86_64-linux.nanofil        # everything; must pass before pushing
```

- Run Prolog with stdin closed (`</dev/null`).
- A 200-function `gen.py` corpus takes GBs of RAM; run one at a time.
- Show that a new test can fail: plant the bug it targets, watch it fail,
  restore. Say so in the commit or report.
- The Trealla DCG translator rejects an if-then chain without a final
  else inside `-->` bodies; end chains with `; []`.

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
  (root AGENTS.md). If the rebase conflicts in a shared file, resolve it
  keeping both sides' intent and rerun the check.
- Report back with what changed, the evidence (commands and decisive
  output), and anything you decided that others should know.
