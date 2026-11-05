# settimeofday(NULL, tz) reaches the kernel instead of stopping the program
# (patches/filc-glibc-settimezone.patch).
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-glibc-settimezone-check";
  dontUnpack = true;
  buildPhase = ''
    $CC -O2 ${./glibc-settimezone.c} -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
