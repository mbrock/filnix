# C++20 coroutines (lowered before FilPizlonator) and musttail calls. A
# musttail call pops its frame only when its caller roots the arguments, so
# symmetric transfer uses stack and musttail.c is only constant-stack at -O2,
# where its pointer argument is the caller's own argument.
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-cxx-coroutines-check";
  dontUnpack = true;
  buildPhase = ''
    for opt in -O0 -O2; do
      $CXX -std=c++20 $opt ${./cxx-coroutine-task.cpp} -o task
      ./task 10000 | tee task.log
      grep -q 'leaf6,\[seven\],leaf8' task.log
      grep -q 'deep=10001' task.log
      $CXX -std=c++20 $opt ${./cxx-coroutine-gc.cpp} -o gc
      ./gc | grep -q 'ok allocs=2000 frees=2000'
      $CXX -std=c++20 $opt ${./cxx-coroutine-uaf.cpp} -o uaf
      if ./uaf > uaf.log 2>&1; then
        echo "resuming a destroyed coroutine was not caught" >&2
        exit 1
      fi
      grep -q 'pointer to free object' uaf.log
      $CC $opt ${./musttail-root.c} -o musttail-root
      ./musttail-root | grep -q 'p is live, tag 42'
    done
    $CC -O2 ${./musttail.c} -o musttail
    ./musttail | grep -q 'qbcdefghijklmnop 1'
  '';
  installPhase = ''
    touch "$out"
  '';
}
