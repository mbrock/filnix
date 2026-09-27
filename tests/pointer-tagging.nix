# Which pointer-tagging patterns keep their capabilities (docs/filc-findings.md).
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-pointer-tagging-check";
  dontUnpack = true;
  buildPhase = ''
    for opt in -O0 -O2; do
      $CC $opt ${./pointer-tagging.c} -o tagging
      ./tagging 2>/dev/null
    done
  '';
  installPhase = "touch $out";
}
