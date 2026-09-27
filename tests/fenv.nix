{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-fenv-check";
  dontUnpack = true;
  buildPhase = ''
    $CC -O2 -frounding-math -D_GNU_SOURCE ${./fenv.c} -lm -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
