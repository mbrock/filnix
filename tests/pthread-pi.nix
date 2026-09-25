{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-pthread-pi-check";
  dontUnpack = true;
  buildPhase = ''
    $CC ${./pthread-pi.c} -pthread -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
