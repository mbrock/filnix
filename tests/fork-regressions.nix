# Compiler and runtime fixes in the mbrock/fil-c fork, each found by a port:
# __sync pointer atomics (cffi), unions inside by-value records (fmt), and
# floating-point exception flags at program start (fmt).
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-fork-regressions-check";
  dontUnpack = true;
  buildPhase = ''
    for opt in -O0 -O2; do
      $CC $opt ${./fork-regressions/sync-pointer-atomics.c} -o sync
      ./sync | grep -qx '42 7 7 42 (nil)'
      $CXX -std=c++17 $opt ${./fork-regressions/union-record-abi.cpp} -o union
      ./union | grep -qx '42 42 42'
      $CC $opt ${./fork-regressions/fenv-startup.c} -o fenv
      ./fenv | grep -qx 'flags 0'
    done
  '';
  installPhase = "touch $out";
}
