# Kept separate from build-filc.nix: never replaces the shared toolchain libc.
{ pkgs }:
let
  compiler = import ../build-filc.nix {
    inherit pkgs;
    filc0 = (import ../compiler/filc0.nix { inherit pkgs; }).filc0;
  };
in
compiler.filc-glibc.overrideAttrs (old: {
  pname = "filc-glibc-cancel-probe";
  patches = (old.patches or [ ]) ++ [
    ../patches/glibc-filc-cancellation-signals.patch
    ../patches/glibc-filc-pause-cancel.patch
  ];
  postPatch = old.postPatch + ''
    substituteInPlace nptl/pthread_cancel.c \
      --replace-fail '#ifdef SHARED' '#if defined(SHARED) && !defined(__FILC__)'
  '';
})
