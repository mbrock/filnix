# brk, sched_setattr and pidfd_spawn fail instead of stopping the program
# (patches/filc-glibc-unsupported-syscalls.patch).
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-glibc-syscall-fallbacks-check";
  dontUnpack = true;
  buildPhase = ''
    $CC -O2 ${./glibc-syscall-fallbacks.c} -o check
    ./check
  '';
  installPhase = ''
    touch "$out"
  '';
}
