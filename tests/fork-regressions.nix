# Compiler and runtime fixes in the mbrock/fil-c fork, each found by a port:
# __sync pointer atomics (cffi), unions inside by-value records (fmt),
# function descriptors that bind locally, so RTLD_LOCAL isolates same-named
# functions (SDL_compat), and unwinds that survive a cleanup throwing and
# catching its own exception, or a switch to a fiber that does (Nix); and
# PHP 8.5 allocator work: small payload memmove/memset through libc, and
# FUGC keeping freshly swept pages from the scavenger until they are reused,
# and a glibc memcmp that does not heap-allocate on every call.
{ pkgsFilc }:
let
  cases = {
    sync-pointer-atomics = ''
      $CC $opt ${./fork-regressions/sync-pointer-atomics.c} -o sync
      ./sync | grep -qx '42 7 7 42 (nil)'
    '';
    union-record-abi = ''
      $CXX -std=c++17 $opt ${./fork-regressions/union-record-abi.cpp} -o union
      ./union | grep -qx '42 42 42'
    '';
    cas-expected-cap = ''
      $CXX -std=c++17 $opt ${./fork-regressions/cas-expected-cap.cpp} -pthread -o cas
      for iteration in $(seq 1 5); do
        timeout 120 ./cas
      done
    '';
    descriptors = ''
      D=${./fork-regressions/descriptors}
      $CC $opt -shared -fPIC $D/a.c -o liba.so
      # Clang may fold same-TU calls at -O2 unless interposition is explicit.
      $CC $opt -fsemantic-interposition -shared -fPIC $D/b.c -o libb.so
      $CC $opt $D/main.c -L. -la -Wl,-rpath,$PWD -o main
      ./main $PWD/libb.so | tee desc.log
      grep -qx 'which()=1 dlsym(which)()=2 callwhich()=1 whichptr()()=1' desc.log
      $CC $opt -fsemantic-interposition -shared -fPIC -Wl,-Bsymbolic $D/b.c -o libb.so
      ./main $PWD/libb.so | tee desc-symbolic.log
      grep -qx 'which()=1 dlsym(which)()=2 callwhich()=2 whichptr()()=2' desc-symbolic.log
    '';
    nested-cleanup = ''
      E=${./fork-regressions/exception-unwind}
      $CXX $opt $E/nested-cleanup.cpp -o nested
      ./nested > nested.log
      printf 'outer caught outer after 6 inner catches\nagain outer\n' > nested.expected
      cmp nested.expected nested.log
    '';
    payload-memops = ''
      $CC $opt ${./fork-regressions/payload-memops.c} -pthread -o memops
      timeout 300 ./memops | grep -qx 'payload memops ok'
    '';
    memcmp-noalloc = ''
      $CC $opt ${./fork-regressions/memcmp-noalloc.c} -o memcmp
      timeout 300 ./memcmp | tee memcmp.log
      grep -qx 'memcmp noalloc ok' memcmp.log
    '';
    scavenge-hold = ''
      $CC $opt ${./fork-regressions/scavenge-hold.c} -o hold
      FUGC_SCAVENGE_HOLD_MS=3000 timeout 120 ./hold | tee hold.log
      grep -qx 'scavenge hold ok' hold.log
    '';
    fiber-unwind = ''
      E=${./fork-regressions/exception-unwind}
      $CXX $opt $E/fiber.cpp -o fiber
      ./fiber > fiber.log
      printf 'coroutine unwound\nmain caught: from coroutine\n' > fiber.expected
      cmp fiber.expected fiber.log
    '';
  };
  tests = pkgsFilc.lib.mapAttrs (
    name: body:
    pkgsFilc.stdenv.mkDerivation {
      name = "filc-fork-${name}-check";
      dontUnpack = true;
      buildPhase = ''
        export FUGC_THREADS=2
        for opt in -O0 -O2; do
          ${body}
        done
      '';
      installPhase = "touch $out";
    }
  ) cases;
in
pkgsFilc.runCommand "filc-fork-regressions-check"
  { passthru = { inherit tests; }; }
  ''
    test -e ${pkgsFilc.lib.concatStringsSep " -a -e " (map toString (builtins.attrValues tests))}
    touch $out
  ''
