# The nanofil playground as a static site: nanofil on swipl-wasm in the
# browser, drawing what it makes of a C file with dterm (README.md).
#
#   nix build -f nanofil/web/play -o /tmp/play-site
#   python3 -m http.server -d /tmp/play-site
{
  flake ? builtins.getFlake (toString ../../..),
  pkgs ? import flake.inputs.nixpkgs { system = "x86_64-linux"; },
  filcc ? flake.packages.x86_64-linux.filcc-staging,
}:
let
  swiplWasm = pkgs.fetchzip {
    url = "https://registry.npmjs.org/swipl-wasm/-/swipl-wasm-8.2.5.tgz";
    sha256 = "15vgsrg3dmzvbc9a720qdgy3wc3yss7g1dxylfcjwk9fy40iwl0q";
  };
in
pkgs.runCommand "nanofil-play"
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      pkgs.python3
    ];
    src = pkgs.lib.fileset.toSource {
      root = ../..;
      fileset = pkgs.lib.fileset.unions [
        ../../bin
        ../../src
        ../dterm.pl
        ../dterm.css
        ../dterm.js
        ./.
      ];
    };
  }
  ''
    cp -r $src nanofil && chmod -R u+w nanofil
    patchShebangs nanofil
    LANG=C.UTF-8 FILCC=${filcc}/bin/clang SWIPL=swipl \
      SWIPL_WASM=${swiplWasm}/dist/swipl nanofil/web/play/build.sh $out
  ''
