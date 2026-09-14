{ pkgs, pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-icu-consumer-check";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.pkg-config ];
  buildInputs = [ pkgsFilc.icu76 ];
  buildPhase = ''
    $CXX ${./icu.cpp} $(pkg-config --cflags --libs icu-uc icu-i18n) -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
