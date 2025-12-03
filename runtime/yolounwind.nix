# Build yolounwind stub library
#
# This provides stub implementations of unwind symbols needed by
# yolo-glibc and compiler-rt's GCC personality function.
# All functions just trap - the yolo runtime doesn't actually unwind.
{ pkgs }:

let
  lib = import ../lib { inherit pkgs; };
  sources = import ../lib/sources.nix { inherit pkgs; };
  inherit (lib) setupCcache llvm;

in
{
  yolounwind = pkgs.stdenv.mkDerivation {
    pname = "filc-yolounwind";
    version = "git";
    src = sources.yolounwind-src;

    nativeBuildInputs = with pkgs; [
      gnumake
      llvm.clang
      ccache
    ];

    preConfigure = ''
      ${setupCcache}
      cd yolounwind
    '';

    buildPhase = ''
      runHook preBuild
      make -j$NIX_BUILD_CORES
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      mkdir -p $out/lib
      cp libyolounwind.a $out/lib/
      runHook postInstall
    '';

    enableParallelBuilding = true;
    meta.description = "Fil-C yolounwind stub library";
  };
}

