# Compiler and runtime fixes in the mbrock/fil-c fork, each found by a port:
# __sync pointer atomics (cffi), unions inside by-value records (fmt),
# function descriptors that bind locally, so RTLD_LOCAL isolates same-named
# functions (SDL_compat), and unwinds that survive a cleanup throwing and
# catching its own exception, or a switch to a fiber that does (Nix). The
# runtime still raises FE_INEXACT in the program (see docs/filc-findings.md),
# so fenv-*.c are not run yet.
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
      D=${./fork-regressions/descriptors}
      $CC $opt -shared -fPIC $D/a.c -o liba.so
      $CC $opt -shared -fPIC $D/b.c -o libb.so
      $CC $opt $D/main.c -L. -la -Wl,-rpath,$PWD -o main
      ./main $PWD/libb.so | tee desc.log
      grep -q 'dlsym(which)()=2' desc.log
      E=${./fork-regressions/exception-unwind}
      $CXX $opt $E/nested-cleanup.cpp -o nested
      ./nested | grep -qx 'outer caught outer after 6 inner catches'
      $CXX $opt $E/fiber.cpp -o fiber
      ./fiber | grep -qx 'main caught: from coroutine'
    done
  '';
  installPhase = "touch $out";
}
