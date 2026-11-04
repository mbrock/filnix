# prctl's capability options reach the kernel
# (patches/filc-runtime-prctl-caps.patch).
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-runtime-prctl-caps-check";
  dontUnpack = true;
  buildPhase = ''
    $CC -O2 ${./runtime-prctl-caps.c} -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
