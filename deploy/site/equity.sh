#!/usr/bin/env bash
# Adds what needs the licensed Equity typeface to a built site, before
# prepare.py pins it: the webfonts style.css loads (fonts/equity/*.woff2)
# and a PDF of each nanofil document, linked from its page.
#
#   deploy/site/equity.sh SITE
#
# The OTFs are mbrock's, licensed for his own sites and PDFs (MB Type
# license: WOFF2 on up to three sites, PDF embedding, conversion with the
# notices kept), and must never be committed or served: they live in the
# private R2 bucket under private/fonts/equity/, which the Worker never
# maps to a URL, and here only in a temporary directory. The site gets
# only WOFF2 files and PDFs. Needs the R2 credentials (AWS_*) and Nix;
# run from the repository root.
set -euo pipefail
site=${1:?usage: equity.sh SITE}
if [[ -z ${AWS_ACCESS_KEY_ID:-} ]]; then
  echo "equity.sh: no R2 credentials; prose stays in Georgia and no PDFs are made" >&2
  exit 0
fi
bucket=filnix-site
aws_args=(--endpoint-url "https://d66b4fdcf8b2d4b0949d7fa3518b9b58.r2.cloudflarestorage.com")
fonts=$(mktemp -d)
trap 'rm -rf "$fonts"' EXIT

for style in Regular Italic Bold; do
  aws "${aws_args[@]}" s3 cp --no-progress \
    "s3://$bucket/private/fonts/equity/EquityOTA-$style.otf" "$fonts/"
done

nixpkgs='import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }'
chmod -R u+w "$site"
mkdir -p "$site/fonts/equity"
nix shell --impure --expr "($nixpkgs).python3.withPackages (p: [ p.fonttools p.brotli ])" -c \
  python3 - "$fonts" "$site/fonts/equity" <<'PY'
import sys
from pathlib import Path
from fontTools.ttLib import TTFont
src, out = map(Path, sys.argv[1:])
for style in ("Regular", "Italic", "Bold"):
    font = TTFont(src / f"EquityOTA-{style}.otf")
    font.flavor = "woff2"  # name table, copyright and trademark kept
    font.save(out / f"equity-{style.lower()}.woff2")
    print(f"fonts/equity/equity-{style.lower()}.woff2")
PY

tool=$(nix build --no-link --print-out-paths --impure --expr \
  "import ./nanofil/web/typst/typeset.nix { pkgs = $nixpkgs; }")
for page in "$site"/nanofil/*.html; do
  grep -q '<article class="dterm guide">' "$page" || continue
  name=$(basename "$page" .html)
  EQUITY_FONTS=$fonts "$tool/bin/dterm-pdf" "$page" -o "$site/nanofil/$name.pdf"
  sed -i "0,/<span class=\"status-right\">/s||<span class=\"status-right\"><a class=\"pdf\" href=\"$name.pdf\">PDF</a> · |" "$page"
done
