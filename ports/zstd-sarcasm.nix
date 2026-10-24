{ pkgs, zstd }:
let
  # The tagged parser lacks statement splitting needed by zstd's macros.
  # Keep this backport local to the experimental port, not the toolchain.
  assembler =
    (import ../packages/sarcasm.nix {
      inherit pkgs;
      sources = zstd.stdenv.cc.sources;
    }).overrideAttrs
      (old: {
        patches = (old.patches or [ ]) ++ [
          ../patches/sarcasm-zstd-statements.patch
        ];
      });
in
zstd.overrideAttrs (old: {
  pname = "zstd-sarcasm";
  patches = (old.patches or [ ]) ++ [
    ../patches/zstd-sarcasm.patch
  ];
  env = (old.env or { }) // {
    NIX_CFLAGS_COMPILE =
      pkgs.lib.replaceStrings [ "-DZSTD_DISABLE_ASM" ] [ "" ] (
        (old.env or { }).NIX_CFLAGS_COMPILE or ""
      )
      + " --filc-resource-dir=${assembler}";
  };
  passthru = (old.passthru or { }) // {
    inherit assembler;
  };
})
