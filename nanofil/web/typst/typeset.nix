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
    pkgs.dm-mono
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
    # EQUITY_FONTS, a directory with the licensed Equity OTFs, sets prose
    # in Equity; without it, prose is Source Serif 4.
    export TYPESET_FONTS=''${EQUITY_FONTS:+$EQUITY_FONTS:}${
      pkgs.lib.concatMapStringsSep ":" (f: "${f}/share/fonts") fonts
    }
    case "''${1:-}" in
      # A page already drawn, in the wiki's layout (deploy/site/equity.sh).
      *.html) exec python3 nanofil/web/typst/typeset.py "$@" ;;
      *) exec bash nanofil/web/typst/pdf.sh "$@" ;;
    esac
  '';
}
