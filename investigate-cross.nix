# Systematic investigation of cross-compilation overlay behavior
# Goal: Understand why dependencies don't use overlayed packages

let
  nixpkgs-filc = /home/mbrock/nixpkgs;
  system = "x86_64-linux";

  # Test 1: No cross-compilation, just regular overlay
  test1 = import nixpkgs-filc {
    inherit system;
    overlays = [
      (final: prev: {
        zlib = prev.zlib.overrideAttrs (old: {
          name = "TEST1-ZLIB-${old.version}";
        });
      })
    ];
  };

  # Test 2: Cross-compilation, no overlay
  test2 = import nixpkgs-filc {
    localSystem = system;
    crossSystem = { config = "x86_64-unknown-linux-filc"; };
  };

  # Test 3: Cross-compilation with crossOverlay
  test3 = import nixpkgs-filc {
    localSystem = system;
    crossSystem = { config = "x86_64-unknown-linux-filc"; };
    crossOverlays = [
      (final: prev: {
        zlib = prev.zlib.overrideAttrs (old: {
          name = "TEST3-ZLIB-${old.version}";
        });
      })
    ];
  };

  # Test 4: Cross-compilation with regular overlay (not crossOverlay)
  test4 = import nixpkgs-filc {
    localSystem = system;
    crossSystem = { config = "x86_64-unknown-linux-filc"; };
    overlays = [
      (final: prev: {
        zlib = prev.zlib.overrideAttrs (old: {
          name = "TEST4-ZLIB-${old.version}";
        });
      })
    ];
  };

  # Custom package that depends on zlib
  customPkg = { stdenv, zlib, fetchurl }:
    stdenv.mkDerivation {
      pname = "custom-pkg";
      version = "1.0";
      src = fetchurl {
        url = "https://ftp.gnu.org/gnu/hello/hello-2.12.1.tar.gz";
        hash = "sha256-jZkUKv2SV28wsM18tCqNxoCZmLxdYH2Idh9RLibH2yA=";
      };
      buildInputs = [ zlib ];
    };

in
{
  # Observations to make:
  inherit test1 test2 test3 test4;

  # Test 1: Does zlib overlay apply in normal (non-cross) case?
  test1_zlib_name = test1.zlib.name;
  test1_file_uses_overlayed_zlib = test1.file.name;  # Does file see TEST1-ZLIB?

  # Test 2: What's the zlib in cross without overlay?
  test2_zlib_name = test2.zlib.name;
  test2_zlib_config = test2.zlib.stdenv.hostPlatform.config;

  # Test 3: Does crossOverlay apply?
  test3_zlib_name = test3.zlib.name;
  test3_file_name = test3.file.name;

  # Test 4: Does regular overlay apply in cross?
  test4_zlib_name = test4.zlib.name;
  test4_file_name = test4.file.name;

  # Test custom package with callPackage
  test3_custom = test3.callPackage customPkg { };
  test3_custom_name = (test3.callPackage customPkg { }).name;
}

