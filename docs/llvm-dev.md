# Hacking on the Fil-C compiler without Nix rebuilds

`nix build .#filcc` builds clang (filc0) from scratch whenever its source
changes. For compiler work, use the `filc-llvm` dev shell instead: it builds
clang incrementally with ninja in a git worktree and gives you `clang`/`clang++`
wrappers that run that clang with the pinned Nix-built Fil-C runtime (libpizlo,
glibc, libc++, headers).

```sh
# One-time: a sparse worktree of fil-c at the revision filnix pins.
nix develop .#filc-llvm -c filc-llvm-worktree ~/fil-c ~/fil-c-dev my-branch

export FILC_SRC=~/fil-c-dev              # default: ~/fil-c-dev
nix develop .#filc-llvm
filc-llvm-build                          # configure if needed, then ninja clang
filc-llvm-build clang opt llvm-dis       # any ninja targets
clang++ -std=c++20 test.cpp -o test      # dev clang + pinned runtime
```

The build directory is `$FILC_DEV_LLVM` (default `$FILC_SRC/build-filnix`). It
uses the CMake options from `compiler/filc0.nix`, but links with lld and split
DWARF so relinking clang after an edit takes seconds rather than minutes.
`filc-llvm-configure` reruns CMake and forwards extra `-D` options.

The wrappers read `$FILC_DEV_LLVM` when they run and disable ccache. ccache
keys on the wrapper, which stays the same when the dev clang changes. The
runtime libraries were compiled by the pinned clang, which is fine for pass
and CodeGen changes that keep the ABI.

`filc-llvm` starts from the official release. For fork experiments, use
`nix develop .#filc-llvm-staging` instead, including for the worktree creation
command. It uses the staging revision and pinned staging runtime. Worktree
creation fetches from the selected pin's repository, not an assumed `origin`.
Choose a separate worktree/build directory when working on both variants.

When a change works, commit it on the worktree branch and push it to the fork.
Update only the staging pin; do not replace the ordinary release pin:

```sh
python3 scripts/update-filc-source-hashes.py --variant staging \
  --repo ~/fil-c --rev <commit>
```

Sources whose files did not change keep their hashes and are not rebuilt.
Staging changes to compiler semantics, capability tracking, GC or runtime still
need soundness review and targeted regressions. A successful package build alone
is not that review. ABI-changing experiments must rebuild their runtime and
libraries; the development compiler substitution deliberately does not do so.
