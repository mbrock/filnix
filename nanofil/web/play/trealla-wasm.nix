# Trealla as a WASI command (tpl.wasm), at the revision and with the
# patches nanofil runs on natively (../../nix/trealla.nix), for the
# playground. trealla-js 0.30.1 traps on nanofil's pipeline ("function
# signature mismatch"), and lacks those patches.
#
#   nix build -f nanofil/web/play/trealla-wasm.nix
{
  pkgs ? import (builtins.getFlake (toString ../../..)).inputs.nixpkgs {
    system = "x86_64-linux";
  },
}:
let
  native = import ../../nix/trealla.nix { inherit pkgs; };
  wasi = pkgs.pkgsCross.wasi32;
in
pkgs.stdenvNoCC.mkDerivation {
  pname = "trealla-wasm";
  inherit (native) version src patches;
  nativeBuildInputs = [
    wasi.stdenv.cc
    pkgs.stdenv.cc
    pkgs.binaryen
    pkgs.xxd
  ];
  postPatch = native.postPatch or "";
  buildPhase = ''
    runHook preBuild
    make -j$NIX_BUILD_CORES WASI=1 WASI_CC=${wasi.stdenv.cc.targetPrefix}cc \
      HOST_CC=cc OPT='-O3 -DNDEBUG' GIT_VERSION='"${native.version}-filnix"' tpl.wasm
    wasm-opt --enable-bulk-memory --enable-nontrapping-float-to-int \
      --enable-sign-ext --enable-mutable-globals -O3 tpl.wasm -o tpl-opt.wasm
    runHook postBuild
  '';
  installPhase = ''
    mkdir -p $out
    cp tpl.wasm $out/tpl-unopt.wasm
    cp tpl-opt.wasm $out/tpl.wasm
  '';
}
