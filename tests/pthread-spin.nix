{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-pthread-spin-check";
  dontUnpack = true;
  buildPhase = ''
    $CC ${./pthread-spin.c} -pthread -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
