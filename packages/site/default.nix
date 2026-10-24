# The GitHub Pages site: pages/ as is, docs/ rendered with pandoc into
# docs/*.html, nanofil's Prolog drawn as terms into nanofil/*.html by
# nanofil/web/dterm.pl, and the nanofil playground in nanofil/play/.
# .github/workflows/pages.yml publishes it.
{ pkgs, filcc }:
let
  inherit (pkgs) lib;
  # One SWI-Prolog for the dterm pages, the playground's build and the
  # playground in the browser (swipl-wasm is 10.1.19).
  swipl = import ../../nanofil/web/play/swipl.nix { inherit pkgs; };
  play = import ../../nanofil/web/play { inherit pkgs filcc swipl; };
  src = lib.fileset.toSource {
    root = ../..;
    fileset = lib.fileset.unions [
      ../../docs
      ../../pages
      ../../nanofil/src
      ../../nanofil/web
    ];
  };
in
pkgs.runCommand "filnix-site"
  {
    nativeBuildInputs = [
      pkgs.pandoc
      swipl
    ];
  }
  ''
    bash ${./.}/build.sh ${src} $out
    cp -r ${play} $out/nanofil/play
  ''
