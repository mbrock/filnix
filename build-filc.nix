# Build the complete Fil-C compiler with all dependencies
{
  base,
  lib,
  sources,
}:

let
  # Build yolo-glibc (no compiler needed)
  yolo = import ./runtime/yolo-glibc.nix { inherit base lib sources; };

  # Build the actual LLVM/Clang compiler
  filc0 = (import ./compiler/filc0.nix { inherit base lib sources; }).filc0;

  # Base filc compiler (overridable)
  filc = base.lib.makeOverridable (import ./compiler/filc.nix) {
    inherit base lib filc0 sources yolo;
  };

  # Build libpizlo
  libpizlo = (import ./runtime/libpizlo.nix {
    inherit base lib sources filc;
  }).libpizlo;

  # Build filc-glibc
  filc-glibc = (import ./runtime/filc-glibc.nix {
    inherit base lib sources libpizlo;
    filc = filc.override { inherit libpizlo; };
  }).filc-glibc;

  # Build libcxx
  filc-libcxx = (import ./compiler/libcxx.nix {
    inherit base lib sources libpizlo filc-glibc;
    filc = filc.override {
      inherit libpizlo;
      filc-libc = filc-glibc;
    };
  }).filc-libcxx;

  # Final compiler with everything
  filc-complete = filc.override {
    inherit libpizlo filc-libcxx;
    filc-libc = filc-glibc;
  };

in
filc-complete
// {
  # Expose build components as attributes
  inherit (yolo) yolo-glibc yolo-glibc-impl;
  inherit libpizlo filc-libcxx filc0;

  # Expose libc with generic name
  filc-libc = filc-glibc;

  # Also expose with specific name for direct access
  inherit filc-glibc;

  # Fil-C headers
  filc-stdfil-headers = "${sources.libpas-src}/filc/include";
}

