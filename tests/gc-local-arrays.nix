{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-gc-local-arrays-check";
  dontUnpack = true;
  buildPhase = ''
    $CC -O0 ${./gc-local-arrays.c} -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
