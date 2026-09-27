{
  pkgs,
  # When true, the final compiler wrapper runs the clang binary from an
  # out-of-Nix LLVM build directory named by $FILC_DEV_LLVM at run time.
  # Runtime libraries (libpizlo, glibc, libc++) still come from the pinned
  # Nix-built compiler, so only the compiler itself is swapped.
  devLlvm ? false,
}:
let
  lib = import ./lib { inherit pkgs; };
  filc0 = (import ./compiler/filc0.nix { inherit pkgs; }).filc0;
  filc-pinned = import ./build-filc.nix { inherit pkgs filc0; };

  filc0-dev = pkgs.runCommand "filc0-dev" { } ''
    mkdir -p $out/bin
    ln -s ${filc0}/lib $out/lib
    cat > $out/bin/clang-${lib.llvmMajor} <<'EOF'
    #!${pkgs.runtimeShell}
    : "''${FILC_DEV_LLVM:?set FILC_DEV_LLVM to a Fil-C LLVM build directory}"
    exec -a "$0" "$FILC_DEV_LLVM/bin/clang-${lib.llvmMajor}" "$@"
    EOF
    chmod +x $out/bin/clang-${lib.llvmMajor}
  '';

  filc =
    if devLlvm then filc-pinned.override { filc0 = filc0-dev; } else filc-pinned;
  filc-binutils = import ./toolchain/binutils.nix { inherit pkgs; };
  filc-sysroot = import ./toolchain/sysroot.nix {
    inherit pkgs;
    filc = filc-pinned;
  };
  toolchain = import ./toolchain/wrappers.nix {
    inherit
      pkgs
      filc
      filc-sysroot
      filc-binutils
      ;
    # ccache keys on the wrapper, which does not change when the dev clang does.
    useCcache = !devLlvm;
  };
in
toolchain.filcc
