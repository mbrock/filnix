# Shell for hacking on the Fil-C LLVM/Clang (FilPizlonator, clang CodeGen)
# outside Nix with incremental ninja builds. See docs/llvm-dev.md.
{ pkgs }:

let
  lib = import ../lib { inherit pkgs; };
  filc0 = import ../compiler/filc0.nix { inherit pkgs; };
  sources = import ../lib/sources.nix { inherit pkgs; };
  filcc-dev = import ../toolchain.nix {
    inherit pkgs;
    devLlvm = true;
  };

  cmakeArgs = pkgs.lib.escapeShellArgs (
    lib.cmakeFlags (
      filc0.cmakeOptions
      // {
        # Faster relinks than gold for the edit/build loop.
        LLVM_USE_LINKER = "lld";
        LLVM_USE_SPLIT_DWARF = true;
        CMAKE_C_COMPILER_LAUNCHER = "ccache";
        CMAKE_CXX_COMPILER_LAUNCHER = "ccache";
      }
    )
  );

  configure = pkgs.writeShellScriptBin "filc-llvm-configure" ''
    set -eu
    exec cmake -S "$FILC_SRC/llvm" -B "$FILC_DEV_LLVM" -G Ninja ${cmakeArgs} "$@"
  '';

  build = pkgs.writeShellScriptBin "filc-llvm-build" ''
    set -eu
    [ -f "$FILC_DEV_LLVM/build.ninja" ] || filc-llvm-configure
    if [ $# -eq 0 ]; then set -- clang; fi
    exec ninja -C "$FILC_DEV_LLVM" "$@"
  '';

  worktree = pkgs.writeShellScriptBin "filc-llvm-worktree" ''
    # usage: filc-llvm-worktree <existing fil-c clone> <new worktree dir> <branch>
    # Creates a sparse worktree at the revision filnix pins (${sources.coreRev}).
    set -eu
    git -C "$1" fetch origin ${sources.coreRev}
    git -C "$1" worktree add --no-checkout -b "$3" "$2" ${sources.coreRev}
    git -C "$2" sparse-checkout set --no-cone \
      /LLVM-LICENSE.txt /llvm/ /clang/ /cmake/ /third-party/ \
      /libcxx/ /libcxxabi/ /libc/ /runtimes/ /filc/ /libpas/
    git -C "$2" checkout "$3"
  '';
in
pkgs.mkShell {
  name = "filc-llvm";
  packages = [
    pkgs.cmake
    pkgs.ninja
    pkgs.python3
    pkgs.ccache
    pkgs.lld
    pkgs.git
    configure
    build
    worktree
    filcc-dev
  ];

  shellHook = ''
    export FILC_SRC="''${FILC_SRC:-$HOME/fil-c-dev}"
    export FILC_DEV_LLVM="''${FILC_DEV_LLVM:-$FILC_SRC/build-filnix}"
    echo "Fil-C LLVM dev shell"
    echo "  FILC_SRC=$FILC_SRC"
    echo "  FILC_DEV_LLVM=$FILC_DEV_LLVM"
    echo "  filc-llvm-build [targets]   (default: clang)"
    echo "  clang / clang++ run the dev clang with the pinned Fil-C runtime"
  '';
}
