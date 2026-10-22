#!/usr/bin/env bash
# Renders scene.py into ../fil-bind.mp4 and ../poster.png with Manim, XeLaTeX,
# Public Sans and ffmpeg from the flake's pinned Nixpkgs (all on
# cache.nixos.org). MEDIA_DIR keeps Manim's LaTeX cache between runs.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
media=${MEDIA_DIR:-$work/media}

pkg() { nix build --no-link --print-out-paths --inputs-from "$root" "nixpkgs#$1"; }
sans=$(pkg public-sans)
dejavu=$(pkg dejavu_fonts)
cat > "$work/fonts.conf" <<EOF
<?xml version="1.0"?>
<!DOCTYPE fontconfig SYSTEM "fonts.dtd">
<fontconfig>
  <dir>$sans/share/fonts</dir>
  <dir>$dejavu/share/fonts</dir>
  <cachedir>$work/fontconfig</cachedir>
</fontconfig>
EOF

cd "$work"
export FILBIND_SLOWDOWN=${FILBIND_SLOWDOWN:-10}
export PUBLIC_SANS=$sans/share/fonts/opentype FONTCONFIG_FILE=$work/fonts.conf
nix shell --inputs-from "$root" nixpkgs#manim nixpkgs#texliveSmall nixpkgs#ffmpeg -c bash -euo pipefail -c '
  manim render --progress_bar none --fps 30 --media_dir "$1" -o fil-bind.mp4 "$2/scene.py" Explainer
  out=$(find "$1/videos" -name fil-bind.mp4 | head -1)
  ffmpeg -v error -y -i "$out" -c:v libx264 -crf 24 -preset slow -pix_fmt yuv420p -movflags +faststart -an \
    "$2/../fil-bind.mp4"
  ffmpeg -v error -y -sseof -0.2 -i "$out" -frames:v 1 -vf scale=1280:720 "$2/../poster.png"
' render "$media" "$here"
