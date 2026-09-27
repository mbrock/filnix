{ pkgs, zstd }:
let
  # The pinned SaRCAsm splits semicolon-separated statements.
  assembler = import ../packages/sarcasm.nix { inherit pkgs; };
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
