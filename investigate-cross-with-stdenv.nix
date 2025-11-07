# Test with replaceCrossStdenv
let
  nixpkgs-filc = /home/mbrock/nixpkgs;
  system = "x86_64-linux";
  pkgs = import <nixpkgs> { inherit system; };

  # Import our actual toolchain
  sources = import ./lib/sources.nix { inherit pkgs; };
  filc0 = (import ./compiler/filc0.nix { inherit pkgs; }).filc0;
  filc = import ./build-filc.nix { inherit pkgs filc0; };
  filc-binutils = import ./toolchain/binutils.nix { inherit pkgs; };
  filc-sysroot = import ./toolchain/sysroot.nix { inherit pkgs filc; };
  toolchain = import ./toolchain/wrappers.nix {
    inherit
      pkgs
      filc
      filc-sysroot
      filc-binutils
      ;
  };

  # Test WITH replaceCrossStdenv AND crossOverlay
  testPkgs = import nixpkgs-filc {
    localSystem = system;
    crossSystem = { config = "x86_64-unknown-linux-filc"; };
    config.replaceCrossStdenv = _: toolchain.filenv;
    crossOverlays = [
      (final: prev: {
        zlib = prev.zlib.overrideAttrs (old: {
          name = "OVERLAY-ZLIB-${old.version}";
        });
      })
    ];
  };

in
{
  zlib_name = testPkgs.zlib.name;
  file_name = testPkgs.file.name;
  hello_name = testPkgs.hello.name;
}

