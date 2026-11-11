# Keep the compiler/runtime fixed and vary only the Huffman assembler.
let
  flake = builtins.getFlake (toString ../..);
  pkgs = import flake.inputs.nixpkgs { system = "x86_64-linux"; };
  filcc = flake.packages.x86_64-linux.filcc-staging;
  base = flake.legacyPackages.x86_64-linux.pkgsFilcStaging.zstd;
  source =
    rev: hash:
    pkgs.fetchgit {
      name = "sarcasm-src";
      url = "https://github.com/mbrock/fil-c";
      inherit rev hash;
      sparseCheckout = [ "projects/sarcasm" ];
    };
  assembler =
    rev: hash:
    (import ../../packages/sarcasm.nix {
      inherit pkgs;
      sources = base.stdenv.cc.sources;
    }).overrideAttrs
      (old: {
        src = source rev hash;
        version = "0-unstable-${builtins.substring 0 12 rev}";
        patches = [ ../../patches/sarcasm-zstd-statements.patch ];
      });
  oldAssembler = assembler "9b7584cea1fa0faf52ffec67859d3b7342919783" "sha256-G/COy4eAbOKvtW8w9SK4VLXvS+CIqa9mI/LOaR7kOkY=";
  newAssembler = assembler "5bf5b21eda6258062cbec43ec5e8f03fe8207983" "sha256-o5NICT6OXc8ZapeEYZMPi/sdXbPQGadTwU9rpurkGfs=";
  safe =
    asm:
    base.overrideAttrs (old: {
      pname = "zstd-fast-flags";
      patches = old.patches ++ [ ../../patches/zstd-sarcasm.patch ];
      env = (old.env or { }) // {
        NIX_CFLAGS_COMPILE =
          pkgs.lib.replaceStrings [ "-DZSTD_DISABLE_ASM" ] [ "" ] (
            (old.env or { }).NIX_CFLAGS_COMPILE or ""
          )
          + " --filc-resource-dir=${asm}";
      };
      passthru = (old.passthru or { }) // {
        assembler = asm;
      };
    });
  before = safe oldAssembler;
  after = safe newAssembler;
in
{
  inherit
    pkgs
    filcc
    base
    oldAssembler
    newAssembler
    before
    after
    ;
  # Use the original upstream assembly ABI for unchecked assembly, not the
  # SaRCAsm-specific virtual-register/frame adaptation.
  yolo = base.overrideAttrs (old: {
    pname = "zstd-yolo";
    patches = old.patches ++ [ ./yolo-forwarders.patch ];
    env = (old.env or { }) // {
      NIX_CFLAGS_COMPILE =
        pkgs.lib.replaceStrings [ "-DZSTD_DISABLE_ASM" ] [ "" ] (
          (old.env or { }).NIX_CFLAGS_COMPILE or ""
        )
        + " -yolo-assembler";
    };
  });
  beforeCheck = import ../../tests/zstd-sarcasm.nix {
    inherit pkgs filcc;
    zstd = before;
  };
  afterCheck = import ../../tests/zstd-sarcasm.nix {
    inherit pkgs filcc;
    zstd = after;
  };
  upstreamAfter = after.overrideAttrs (old: {
    cmakeFlags =
      pkgs.lib.filter (
        flag:
        !(builtins.elem flag [
          "-DZSTD_BUILD_STATIC:BOOL=OFF"
          "-DZSTD_BUILD_TESTS:BOOL=OFF"
        ])
      ) old.cmakeFlags
      ++ [
        "-DZSTD_BUILD_STATIC:BOOL=ON"
        "-DZSTD_BUILD_TESTS:BOOL=ON"
      ];
    doCheck = true;
    checkPhase = ''
      runHook preCheck
      export LD_LIBRARY_PATH="$PWD/lib:''${LD_LIBRARY_PATH:-}"
      ./tests/fuzzer -i100
      ./tests/zstreamtest -i100
      runHook postCheck
    '';
  });
}
