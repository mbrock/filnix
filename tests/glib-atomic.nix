{ pkgs, pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-glib-atomic-check";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.pkg-config ];
  buildInputs = [ pkgsFilc.glib ];
  buildPhase = ''
    $CC -O2 -Werror ${./glib-atomic.c} $(pkg-config --cflags --libs glib-2.0) -o check
    FUGC_THREADS=2 timeout 30 ./check
  '';
  installPhase = ''touch "$out"'';
}
