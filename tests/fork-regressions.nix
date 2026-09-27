# Compiler and runtime fixes in the mbrock/fil-c fork, each found by a port:
# __sync pointer atomics (cffi), unions inside by-value records (fmt), and
# floating-point exception flags at program start and across allocation
# (fmt), and function descriptors that bind locally, so RTLD_LOCAL isolates
# same-named functions (SDL_compat).
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
      $CC $opt ${./fork-regressions/fenv-startup.c} -o fenv -lm
      ./fenv | grep -qx 'flags 0'
      $CC $opt ${./fork-regressions/fenv-alloc.c} -o fenv-alloc -lm
      ./fenv-alloc | grep -qx 'start 0 after-malloc 0 after-free 0'
      D=${./fork-regressions/descriptors}
      $CC $opt -shared -fPIC $D/a.c -o liba.so
      $CC $opt -shared -fPIC $D/b.c -o libb.so
      $CC $opt $D/main.c -L. -la -Wl,-rpath,$PWD -o main
      ./main $PWD/libb.so | tee desc.log
      grep -q 'dlsym(which)()=2' desc.log
    done
  '';
  installPhase = "touch $out";
}
