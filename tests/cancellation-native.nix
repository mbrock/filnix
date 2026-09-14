{ pkgs }:
let
  sources = import ../lib/sources.nix { inherit pkgs; };
  source = pkgs.applyPatches {
    name = "filc-cancellation-native-source";
    src = sources.libpas-src;
    patches = [ ../patches/libpizlo-cancellation.patch ];
  };
in
pkgs.runCommand "filc-cancellation-native-check"
  {
    nativeBuildInputs = [
      pkgs.stdenv.cc
      pkgs.binutils
      pkgs.python3
    ];
  }
  ''
    cc -O2 -Wall -Wextra -Werror -pthread \
      -I${source}/libpas/src/libpas \
      ${./native-syscall-cancel.c} \
      ${source}/libpas/src/libpas/filc_cancel_syscall.S -o native-gate
    python ${./native-syscall-cancel.py} ./native-gate
    touch "$out"
  ''
