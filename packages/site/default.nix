# The GitHub Pages site: pages/ as is, and docs/ rendered with pandoc into
# docs/*.html. .github/workflows/pages.yml publishes it.
{ pkgs }:
let
  inherit (pkgs) lib;
  src = lib.fileset.toSource {
    root = ../..;
    fileset = lib.fileset.unions [
      ../../docs
      ../../pages
    ];
  };
in
pkgs.runCommand "filnix-site" { nativeBuildInputs = [ pkgs.pandoc ]; } ''
  bash ${./.}/build.sh ${src} $out
''
