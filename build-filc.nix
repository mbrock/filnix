# Build the complete Fil-C compiler with all dependencies
{
  pkgs,
  filc0,
}:

let
  sources = import ./lib/sources.nix { inherit pkgs; };

  # Build yolo-glibc (no compiler needed)
  yolo = import ./runtime/yolo-glibc.nix { inherit pkgs; };

  # Base filc compiler (overridable)
  filc = pkgs.lib.makeOverridable (import ./compiler/filc.nix) {
    inherit
      pkgs
      filc0
      yolo
      ;
  };

  # Build libpizlo
  libpizlo =
    (import ./runtime/libpizlo.nix {
      inherit pkgs filc;
    }).libpizlo;

  # Build filc-glibc
  filc-glibc =
    (import ./runtime/filc-glibc.nix {
      inherit pkgs libpizlo;
      filc = filc.override { inherit libpizlo; };
    }).filc-glibc;

  # Build libcxx
  filc-libcxx =
    (import ./compiler/libcxx.nix {
      inherit pkgs filc-glibc;
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
# Use passthru to expose metadata without making them build dependencies
filc-complete.overrideAttrs (old: {
  passthru = (old.passthru or { }) // {
    # Expose build components as attributes (metadata only!)
    inherit (yolo) yolo-glibc yolo-glibc-impl;
    inherit libpizlo filc-libcxx filc0;

    # Expose libc with generic name
    filc-libc = filc-glibc;

    # Also expose with specific name for direct access
    inherit filc-glibc;

    # Fil-C headers
    filc-stdfil-headers = "${sources.libpas-src}/filc/include";
  };
})
