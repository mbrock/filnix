# nftw, ftw, scandirat and fts walk subdirectories
# (patches/filc-glibc-openat-nocancel.patch).
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-glibc-dirwalk-check";
  dontUnpack = true;
  buildPhase = ''
    $CC -O2 ${./glibc-dirwalk.c} -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
