{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-packed-pointer-check";
  dontUnpack = true;
  buildPhase = ''
    $CC -O2 ${./packed-pointer.c} -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
