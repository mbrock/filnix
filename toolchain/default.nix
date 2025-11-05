# Fil-C toolchain: binutils, sysroot, and wrapped compilers
{
  base,
  lib,
  runtime,
  compiler,
}:

let
  binutils-build = import ./binutils.nix { inherit base; };
  inherit (binutils-build) filc-binutils;

  sysroot-build = import ./sysroot.nix {
    inherit
      base
      lib
      runtime
      compiler
      ;
  };
  inherit (sysroot-build) filc-sysroot;

  wrappers = import ./wrappers.nix {
    inherit
      base
      lib
      compiler
      runtime
      filc-sysroot
      filc-binutils
      ;
  };

in
{
  inherit filc-binutils filc-sysroot;
  inherit (wrappers)
    filc-cc
    filc-bintools
    filcc
    filc-aliases
    ;
  inherit (wrappers)
    filenv
    withFilC
    fix
    parallelize
    dontTest
    debug
    ;
}
