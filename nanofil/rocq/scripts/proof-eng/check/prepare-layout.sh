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
# The stage recognizes HLG as the conventional interpreter-logic alias.
# Hello's result is still checked against its abstract-runtime contract; this
# rewrite only lets the alias resolver find the flat declaration's file.
python3 - "$tmp/source" <<'PY'
from pathlib import Path
import re
import sys
for path in Path(sys.argv[1]).glob('PEAudit_*.v'):
    source = re.sub(r"(?<![\w.'])(?:LG|CaseLogic)(?![\w'])", 'HLG', path.read_text())
    source = source.replace('HelloGlibcJoin AuditRuntime.', 'HelloGlibcJoin InterpRuntime.')
    # Query-local aliases must not become global fallback aliases for unrelated
    # library files while the flatten stage builds its namespace index.
    names = re.findall(r'^Module (\w+) := (?!Logic\b)', source, re.M)
    for name in names:
        source = re.sub(r"(?<![\w.'])" + name + r"(?![\w'])",
                        path.stem + '_' + name, source)
    path.write_text(source)
PY
"$here/../apply.sh" "$tmp/source" "$tmp/flat"
for file in "$here"/layouts/original/*.v; do
  name=$(basename "$file" .v | tr - _)
  cp "$tmp/flat/PEAudit_$name.v" "$out/$(basename "$file")"
done
printf '%s\n' '{"Fix.R": "AuditRuntime", "Glibc.Fix.R": "AuditRuntime"}' >"$out/assumption-aliases.json"
