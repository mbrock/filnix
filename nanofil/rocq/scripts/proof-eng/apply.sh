#!/usr/bin/env bash
# Rewrite a copy of the glibc proof tree with every stage in stages/, in
# name order, and then lay the files of overlay/ over the result.
#
#   apply.sh SRC DST    # SRC is rocq/glibc of main; DST is replaced
#
# Each stage is a program called with the tree as its only argument. It
# rewrites the tree in place and must give the same output for the same
# input. overlay/ holds files written by hand: new files, and whole
# replacements of files that no stage can produce.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=$1
dst=$2
rm -rf "$dst"
mkdir -p "$(dirname "$dst")"
cp -r "$src" "$dst"
find "$dst" \( -name '*.vo*' -o -name '*.glob' -o -name '.*.aux' \) -delete
for stage in "$here"/stages/*; do
  echo "@@proof-eng stage $(basename "$stage")" >&2
  case $stage in
    *.py) python3 -I "$stage" "$dst" ;;
    *) "$stage" "$dst" ;;
  esac
done
if [ -d "$here/overlay" ]; then
  cp -r "$here/overlay/." "$dst/"
fi
python3 -I "$here/stages/10-flatten.py" "$dst" --check-names-only
