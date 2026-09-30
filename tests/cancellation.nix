{ pkgs, filcc }:
(pkgs.overrideCC pkgs.stdenv filcc).mkDerivation {
  name = "filc-cancellation-check";
  dontUnpack = true;
  buildPhase = ''
    unset LD_LIBRARY_PATH
    export FUGC_THREADS=2
    for opt in -O0 -O2; do
      $CC $opt -Werror ${./pthread-cancel.c} -pthread -o pause-check
      timeout 60 ./pause-check ${filcc.filc-glibc}
      $CC $opt -Werror -DWITH_CXX_CLEANUP -c ${./pthread-cancel.c} -o pause-check.o
      $CXX $opt -Werror ${./pthread-cancel-cxx.cc} pause-check.o -pthread -o pause-check-cxx
      timeout 60 ./pause-check-cxx ${filcc.filc-glibc}
      $CC $opt -Werror ${./cancellation-semantics.c} -pthread -o semantics
      $CC $opt -Werror -DWITH_CXX_CLEANUP -c ${./cancellation-semantics.c} -o semantics.o
      $CXX $opt -Werror ${./pthread-cancel-cxx.cc} semantics.o -pthread -o semantics-cxx
      for executable in semantics semantics-cxx; do
        for scenario in $(seq 0 27); do
          timeout 60 ./$executable "$scenario"
        done
      done
    done
  '';
  installPhase = ''touch "$out"'';
}
