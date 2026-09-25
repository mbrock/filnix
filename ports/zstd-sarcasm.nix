{ pkgs, zstd }:
let
  # Keep experiments local: the compiler/runtime and default assembler stay pinned.
  assembler =
    (import ../packages/sarcasm.nix { inherit pkgs; }).overrideAttrs
      (old: {
        patches = (old.patches or [ ]) ++ [ ../patches/sarcasm-zstd.patch ];
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
