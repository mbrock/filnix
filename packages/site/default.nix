# The GitHub Pages site: pages/ as is, docs/ rendered with pandoc into
# docs/*.html, and nanofil's Prolog drawn as terms into nanofil/*.html by
# nanofil/web/dterm.pl. .github/workflows/pages.yml publishes it.
{ pkgs }:
let
  inherit (pkgs) lib;
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
pkgs.runCommand "filnix-site" { nativeBuildInputs = [
    pkgs.pandoc
    pkgs.swi-prolog
  ]; } ''
  bash ${./.}/build.sh ${src} $out
''
