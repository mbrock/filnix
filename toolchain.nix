{ pkgs }:
let
  filc0 = (import ./compiler/filc0.nix { inherit pkgs; }).filc0;
  filc = import ./build-filc.nix { inherit pkgs filc0; };
  filc-binutils = import ./toolchain/binutils.nix { inherit pkgs; };
  filc-sysroot = import ./toolchain/sysroot.nix { inherit pkgs filc; };
  toolchain = import ./toolchain/wrappers.nix {
    inherit
      pkgs
      filc
      filc-sysroot
      filc-binutils
      ;
  };
in
toolchain.filcc
