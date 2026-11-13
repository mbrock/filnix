#!/usr/bin/env bash
# Generate reviewable query sources with the same stages as the proof tree.
# Keep these as layout data: a redesigned runtime may need different queries.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${1:?usage: prepare-layout.sh ORIGINAL_TREE OUTPUT_LAYOUT}
out=${2:?usage: prepare-layout.sh ORIGINAL_TREE OUTPUT_LAYOUT}
mkdir -p "$out"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp -r "$src" "$tmp/source"
for file in "$here"/layouts/original/*.v; do
  name=$(basename "$file" .v | tr - _)
  cp "$file" "$tmp/source/PEAudit_$name.v"
done
"$here/../apply.sh" "$tmp/source" "$tmp/flat"
for file in "$here"/layouts/original/*.v; do
  name=$(basename "$file" .v | tr - _)
  cp "$tmp/flat/PEAudit_$name.v" "$out/$(basename "$file")"
done
