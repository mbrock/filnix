# The nanofil playground: nanofil on SWI-Prolog 10.1.19 in WebAssembly,
# drawing what it makes of a C file with dterm (README.md). Its files go
# in the wiki at nanofil/play/ (packages/site), beside the dterm pages
# whose style.css and dterm.css it uses.
{
  flake ? builtins.getFlake (toString ../../..),
  pkgs ? import flake.inputs.nixpkgs { system = "x86_64-linux"; },
  filcc ? flake.packages.x86_64-linux.filcc-staging,
  swipl ? import ./swipl.nix { inherit pkgs; },
}:
let
  swiplWasm = pkgs.fetchzip {
    url = "https://registry.npmjs.org/swipl-wasm/-/swipl-wasm-8.2.5.tgz";
    sha256 = "15vgsrg3dmzvbc9a720qdgy3wc3yss7g1dxylfcjwk9fy40iwl0q";
  };
  # The source editor: editor/editor.js and the CodeMirror packages its
  # package-lock.json pins, bundled and minified into one ES module.
  editor = pkgs.buildNpmPackage {
    name = "nanofil-play-editor";
    src = ./editor;
    npmDepsHash = "sha256-6BiFPSaA5NTanpFJbhQz4ovEjsl1NIukvzdID4kkDok=";
    nativeBuildInputs = [ pkgs.esbuild ];
    buildPhase = ''
      esbuild editor.js --bundle --minify --format=esm --outfile=editor.min.js
    '';
    installPhase = "install -D editor.min.js $out/editor.js";
  };
in
pkgs.runCommand "nanofil-play"
  {
    passthru = { inherit editor; };
    nativeBuildInputs = [
      swipl
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
    cp ${editor}/editor.js $out/
  ''
