#!/usr/bin/env bash
# build.sh SRC OUT FILES OPTIONS NIXPKGS NIX...: render SRC/docs/*.md with
# pandoc into OUT/docs, copy SRC/pages to OUT, draw SRC/nanofil/src/*.pl
# into OUT/nanofil and SRC/nanofil's .v files into OUT/nanofil/rocq,
# render SRC/nanofil/docs/*.md into OUT/nanofil/docs,
# and draw each SRC/NIX file into OUT/nix with the option index (FILES
# lists the repository's paths, for their links; OPTIONS is
# dterm-nix/options.nix's JSON; NIXPKGS the Nixpkgs it read). Fails if a
# doc is missing from docs/README.md or a page links to a docs file that
# does not exist.
set -euo pipefail
src=$1
out=$2
files=$3
options=$4
nixpkgs=$5
shift 5
here=$(cd "$(dirname "$0")" && pwd)

mkdir -p "$out/docs"
cp -r "$src/pages/." "$out/"
# pages/style.css (copied above) is shared by the docs and the pages.
cp "$src"/docs/*.txt "$out/docs/"

for md in "$src"/docs/*.md; do
  name=$(basename "$md" .md)
  echo "$(date -u +%FT%TZ) site: render docs/$name.md"
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
# Rendered in independent derivations, with the same complete cross-file
# indexes and real proof states. Assembly never substitutes a fixture.
cp -r "${PROLOG_PAGES:?the site needs rendered Prolog pages}/." "$out/nanofil/"
cp -r "${ROCQ_PAGES:?the site needs rendered Rocq pages}" "$out/nanofil/rocq"
# The dterm workbench: the samples drawn by dterm, set side by side.
echo "$(date -u +%FT%TZ) site: render dterm workbench"
mkdir -p "$out/nanofil/workbench"
wb=$src/nanofil/web/workbench
cp "$wb"/index.html "$wb"/*.css "$wb"/*.js "$out/nanofil/workbench/"
(cd "$wb" && swipl workbench.pl "$out/nanofil/workbench" "$src/nanofil/src" </dev/null)

# nanofil's own documents: those dterm drew (DTERM_DOCS) are beside its
# pages, README.md, which must list every document, as nanofil/index.html;
# pandoc renders the rest into nanofil/docs/NAME.html.
mkdir -p "$out/nanofil/docs"
cp -r "$src/nanofil/docs/dterm" "$out/nanofil/docs/"
for md in "$src"/nanofil/docs/*.md; do
  name=$(basename "$md" .md)
  [ "$name" = README ] || grep -q "]($name.md" "$src/nanofil/docs/README.md" || {
    echo "nanofil/docs/$name.md is not linked from nanofil/docs/README.md" >&2
    exit 1
  }
  case " ${DTERM_DOCS:?the site needs the list of dterm-drawn documents} " in
  *" $name "*)
    # Drawn by dterm beside the modules; this address forwards there.
    page=$name.html html=$name.html
    [ "$name" = README ] && page=index.html html=index.html
    printf '<!doctype html><meta charset="utf-8"><meta http-equiv="refresh" content="0; url=../%s"><link rel="canonical" href="../%s"><a href="../%s">%s</a>\n' \
      "$page" "$page" "$page" "$name" >"$out/nanofil/docs/$html"
    continue
    ;;
  esac
  echo "$(date -u +%FT%TZ) site: render nanofil/docs/$name.md"
  args=()
  if [ "$(grep -c '^## ' "$md")" -ge 4 ]; then
    args+=(--toc --toc-depth=3)
  fi
  pandoc -f gfm -t html5 --standalone --shift-heading-level-by=-1 \
    --template "$here/template.html" --lua-filter "$here/nanofil-links.lua" \
    -V nanofil -V source="$name.md" "${args[@]}" -o "$out/nanofil/docs/$name.html" "$md"
done

# The archive, nanofil/docs/archive/NAME.md, renders beside the others as
# nanofil/docs/NAME.html, where it always was, marked archived; README.md
# lists each one too.
for md in "$src"/nanofil/docs/archive/*.md; do
  name=$(basename "$md" .md)
  echo "$(date -u +%FT%TZ) site: render nanofil/docs/archive/$name.md"
  grep -q "](archive/$name.md" "$src/nanofil/docs/README.md" || {
    echo "nanofil/docs/archive/$name.md is not linked from nanofil/docs/README.md" >&2
    exit 1
  }
  [ ! -e "$src/nanofil/docs/$name.md" ] || {
    echo "nanofil/docs/archive/$name.md and nanofil/docs/$name.md would both be $name.html" >&2
    exit 1
  }
  args=()
  if [ "$(grep -c '^## ' "$md")" -ge 4 ]; then
    args+=(--toc --toc-depth=3)
  fi
  pandoc -f gfm -t html5 --standalone --shift-heading-level-by=-1 \
    --template "$here/template.html" --lua-filter "$here/nanofil-links.lua" \
    -V nanofil -M archived=true -V source="archive/$name.md" "${args[@]}" \
    -o "$out/nanofil/docs/$name.html" "$md"
done

# filnix's own Nix, drawn by dterm-nix with nanofil's dterm.css and
# dterm.js (../nanofil/).
echo "$(date -u +%FT%TZ) site: render $# Nix pages and option index"
mkdir -p "$out/nix"
cp "$src"/dterm-nix/dterm-nix.css "$src"/dterm-nix/dterm-nix.js "$out/nix/"
(cd "$src" && swipl dterm-nix/dterm_nix.pl "$out/nix" . --files="$files" \
  --options="$options" --nixpkgs="$nixpkgs" "$@" </dev/null)

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
