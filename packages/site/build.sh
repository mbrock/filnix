#!/usr/bin/env bash
# build.sh SRC OUT: render SRC/docs/*.md with pandoc into OUT/docs, copy
# SRC/pages to OUT, draw SRC/nanofil/src/*.pl into OUT/nanofil, and
# render SRC/nanofil/docs/*.md into OUT/nanofil/docs. Fails if a doc is
# missing from docs/README.md or a page links to a docs file that does
# not exist.
set -euo pipefail
src=$1
out=$2
here=$(cd "$(dirname "$0")" && pwd)

mkdir -p "$out/docs"
cp -r "$src/pages/." "$out/"
# pages/style.css (copied above) is shared by the docs and the pages.
cp "$src"/docs/*.txt "$out/docs/"

for md in "$src"/docs/*.md; do
  name=$(basename "$md" .md)
  if [ "$name" = README ]; then
    html=index
  else
    html=$name
    grep -q "]($name.md)" "$src/docs/README.md" || {
      echo "docs/$name.md is not linked from docs/README.md" >&2
      exit 1
    }
  fi
  args=()
  # A table of contents for documents with several sections.
  if [ "$(grep -c '^## ' "$md")" -ge 4 ] && [ "$name" != README ]; then
    args+=(--toc --toc-depth=3)
  fi
  grep -q '^```mermaid' "$md" && args+=(-V mermaid)
  [ "$name" = README ] && args+=(-V index)
  pandoc -f gfm -t html5 --standalone --shift-heading-level-by=-1 \
    --template "$here/template.html" --lua-filter "$here/links.lua" \
    -V source="$name.md" "${args[@]}" -o "$out/docs/$html.html" "$md"
done

mkdir -p "$out/nanofil"
cp "$src"/nanofil/web/dterm.css "$src"/nanofil/web/dterm.js "$out/nanofil/"
# The guide is a dterm page too (nanofil/guide.html); a broken reference
# in it fails the build.
swipl "$src/nanofil/web/dterm.pl" "$out/nanofil" "$src/nanofil/src" \
  --guide="$src/nanofil/docs/guide.md" </dev/null
# The dterm workbench: the samples drawn by dterm, set side by side.
mkdir -p "$out/nanofil/workbench"
wb=$src/nanofil/web/workbench
cp "$wb"/index.html "$wb"/*.css "$wb"/*.js "$out/nanofil/workbench/"
(cd "$wb" && swipl workbench.pl "$out/nanofil/workbench" "$src/nanofil/src" </dev/null)

# nanofil's own documents, beside its pages: nanofil/docs/NAME.html.
mkdir -p "$out/nanofil/docs"
cp -r "$src/nanofil/docs/dterm" "$out/nanofil/docs/"
for md in "$src"/nanofil/docs/*.md; do
  name=$(basename "$md" .md)
  if [ "$name" = guide ]; then
    # Drawn by dterm beside the modules; the old address forwards there.
    printf '<!doctype html><meta charset="utf-8"><meta http-equiv="refresh" content="0; url=../guide.html"><link rel="canonical" href="../guide.html"><a href="../guide.html">The guide</a>\n' >"$out/nanofil/docs/guide.html"
    continue
  fi
  args=()
  if [ "$(grep -c '^## ' "$md")" -ge 4 ]; then
    args+=(--toc --toc-depth=3)
  fi
  pandoc -f gfm -t html5 --standalone --shift-heading-level-by=-1 \
    --template "$here/template.html" --lua-filter "$here/nanofil-links.lua" \
    -V nanofil -V source="$name.md" "${args[@]}" -o "$out/nanofil/docs/$name.html" "$md"
done

status=0
for html in "$out"/nanofil/docs/*.html; do
  for target in $(grep -o 'href="[^"]*"' "$html" | sed 's/^href="//; s/"$//; s/#.*//'); do
    case $target in "" | *:* | ../../*) continue ;; esac
    if [ ! -e "$out/nanofil/docs/$target" ]; then
      echo "nanofil/docs/$(basename "$html"): broken link to $target" >&2
      status=1
    fi
  done
done
for html in "$out"/docs/*.html; do
  for target in $(grep -o 'href="[^"]*"' "$html" | sed 's/^href="//; s/"$//; s/#.*//'); do
    case $target in "" | *:* | ../ | ../*) continue ;; esac
    if [ ! -e "$out/docs/$target" ]; then
      echo "$(basename "$html"): broken link to $target" >&2
      status=1
    fi
  done
done
exit $status
