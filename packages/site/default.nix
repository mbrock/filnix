# The GitHub Pages site: pages/ as is, docs/ rendered with pandoc into
# docs/*.html, nanofil's Prolog drawn as terms into nanofil/*.html by
# nanofil/web/dterm.pl, nanofil's documents (its guide among them) into
# nanofil/docs/*.html, the nanofil playground in nanofil/play/, and
# filnix's own Nix drawn by dterm-nix into nix/*.html.
# .github/workflows/pages.yml publishes it.
{ pkgs, filcc }:
let
  inherit (pkgs) lib;
  # One SWI-Prolog for the dterm pages, the playground's build and the
  # playground in the browser (swipl-wasm is 10.1.19).
  swipl = import ../../nanofil/web/play/swipl.nix { inherit pkgs; };
  play = import ../../nanofil/web/play { inherit pkgs filcc swipl; };
  # The Nix files drawn as pages (dterm-nix), and every path of the
  # repository, which their path links are checked against: a list, so
  # the site does not rebuild for every commit.
  nixPages = [
    "nixos/filc.nix"
    "finix/userland.nix"
    "ports/default.nix"
    "toolchain.nix"
  ];
  repoFiles = builtins.toFile "filnix-files" (
    lib.concatMapStrings (
      f: lib.removePrefix "./" (lib.path.removePrefix ../.. f) + "\n"
    ) (lib.fileset.toList ../..)
  );
  src = lib.fileset.toSource {
    root = ../..;
    fileset = lib.fileset.unions [
      ../../docs
      ../../pages
      ../../nanofil/docs
      ../../nanofil/src
      ../../nanofil/web
      ../../dterm-nix
      (lib.fileset.unions (map (f: ../.. + "/${f}") nixPages))
    ];
  };
in
pkgs.runCommand "filnix-site"
  {
    nativeBuildInputs = [
      pkgs.pandoc
      swipl
    ];
    passthru = { inherit play; };
  }
  ''
    bash ${./.}/build.sh ${src} $out ${repoFiles} ${lib.escapeShellArgs nixPages}
    cp -r ${play} $out/nanofil/play
  ''
