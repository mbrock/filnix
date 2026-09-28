# Match, replace and run the DFA of re2 (and its abseil headers) under Fil-C.
{ pkgs, pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-re2-consumer-check";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.pkg-config ];
  buildInputs = [ pkgsFilc.re2 ];
  buildPhase = ''
    $CXX -std=c++17 -O2 ${./re2.cpp} $(pkg-config --cflags --libs re2) -o check
    ./check | tee check.log
    grep -q '^ok: ' check.log
  '';
  installPhase = ''
    touch "$out"
  '';
}
