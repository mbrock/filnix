# C++20 coroutines (lowered before FilPizlonator) and musttail calls, which
# symmetric transfer depends on to run in bounded stack.
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-cxx-coroutines-check";
  dontUnpack = true;
  buildPhase = ''
    for opt in -O0 -O2; do
      $CXX -std=c++20 $opt ${./cxx-coroutine-task.cpp} -o task
      ./task 1000000 | tee task.log
      grep -q 'leaf6,\[seven\],leaf8' task.log
      grep -q 'deep=1000001' task.log
      $CXX -std=c++20 $opt ${./cxx-coroutine-gc.cpp} -o gc
      ./gc | grep -q 'ok allocs=2000 frees=2000'
      $CXX -std=c++20 $opt ${./cxx-coroutine-uaf.cpp} -o uaf
      if ./uaf > uaf.log 2>&1; then
        echo "resuming a destroyed coroutine was not caught" >&2
        exit 1
      fi
      grep -q 'pointer to free object' uaf.log
      $CC $opt ${./musttail.c} -o musttail
      ./musttail | grep -q 'qbcdefghijklmnop 1'
    done
  '';
  installPhase = ''
    touch "$out"
  '';
}
