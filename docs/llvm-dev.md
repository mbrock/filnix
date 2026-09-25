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

When a change works, commit it on the worktree branch, export it with
`git format-patch`, and add it to `compiler/filc0.nix` so Nix builds pick it
up (or bump `lib/filc-upstream.json` once it lands upstream).
