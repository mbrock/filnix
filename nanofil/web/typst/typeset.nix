# dterm-pdf: pdf.sh with what it needs (README.md).
#
#   nix build --impure -o /tmp/dterm-pdf --expr \
#     'import ./nanofil/web/typst/typeset.nix { pkgs = import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }; }'
#   /tmp/dterm-pdf/bin/dterm-pdf nanofil/docs/lambda-anf.md -o lambda-anf.pdf
{ pkgs }:
let
  # The site's SWI-Prolog, so pages draw exactly as on the wiki.
  swipl = import ../play/swipl.nix { inherit pkgs; };
  fonts = [
    pkgs.public-sans
    pkgs.source-serif
    pkgs.jetbrains-mono
    pkgs.dejavu_fonts
  ];
in
pkgs.writeShellApplication {
  name = "dterm-pdf";
  runtimeInputs = [
    swipl
    pkgs.chromium
    pkgs.typst
    pkgs.python3
    pkgs.coreutils
  ];
  text = ''
    export TYPESET_FONTS=${pkgs.lib.concatMapStringsSep ":" (f: "${f}/share/fonts") fonts}
    exec bash nanofil/web/typst/pdf.sh "$@"
  '';
}
