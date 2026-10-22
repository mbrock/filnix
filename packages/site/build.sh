#!/usr/bin/env bash
# build.sh SRC OUT: render SRC/docs/*.md with pandoc into OUT/docs and copy
# SRC/pages to OUT. Fails if a doc is missing from docs/README.md or a page
# links to a docs file that does not exist.
set -euo pipefail
src=$1
out=$2
here=$(cd "$(dirname "$0")" && pwd)

mkdir -p "$out/docs"
cp -r "$src/pages/." "$out/"
cp "$here/style.css" "$out/docs/"
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

status=0
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
