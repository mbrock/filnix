# Fil-C's LLVM JIT API: build LLVM IR in a Fil-C program, compile it through
# the Fil-C passes in-process, and call it. Needs a toolchain whose pin has
# the JIT (staging).
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-llvm-jit-check";
  dontUnpack = true;
  buildPhase = ''
    for opt in -O0 -O2; do
      $CC $opt -enable-filc-jit ${./llvm-jit/hello.c} -o hello
      ./hello | grep -qx 'Hello!'

      $CC $opt -enable-filc-jit ${./llvm-jit/global.c} -o global
      ./global | grep -qx 'counter 99000 calls 2000 length 20000 sum 9990000'

      # Without -enable-filc-jit the runtime refuses the JIT API.
      $CC $opt ${./llvm-jit/hello.c} -o nojit
      if ./nojit > nojit.log 2>&1; then
        echo "JIT API ran without -enable-filc-jit" >&2
        exit 1
      fi
    done
  '';
  installPhase = "touch $out";
}
