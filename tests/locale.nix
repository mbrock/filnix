{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-utf8-locale-check";
  dontUnpack = true;
  buildPhase = ''
    $CC ${./locale.c} -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
