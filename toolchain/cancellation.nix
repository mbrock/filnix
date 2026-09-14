# Reassemble only the compiler wrappers/sysroot. LLVM, libpizlo, libc++ and
# the ordinary package scope stay cached; callers opt in through stdenv.
{ pkgs, baseStdenv }:
let
  compiler = import ../build-filc.nix {
    inherit pkgs;
    filc0 = (import ../compiler/filc0.nix { inherit pkgs; }).filc0;
  };
  libc = import ../runtime/filc-glibc-cancellation.nix { inherit pkgs; };
  filc = (compiler.override { filc-libc = libc; }).overrideAttrs (old: {
    passthru = (old.passthru or { }) // {
      filc-glibc = libc;
      filc-libc = libc;
    };
  });
  filc-sysroot = import ./sysroot.nix { inherit pkgs filc; };
  filc-binutils = import ./binutils.nix { inherit pkgs; };
  wrapped = import ./wrappers.nix {
    inherit
      pkgs
      filc
      filc-sysroot
      filc-binutils
      ;
  };
in
{
  inherit libc;
  cc = wrapped.filcc;
  stdenv = baseStdenv.override { cc = wrapped.filcc; };
}
