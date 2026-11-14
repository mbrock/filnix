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
# The concrete tree specializes Hello. Its separate abstract-tree audit retains
# the original twelve-assumption contract and checks the original statement.
python3 - "$tmp/source" "$tmp/renames.json" <<'PY'
from pathlib import Path
import json
import re
import sys
renames = {}
for path in Path(sys.argv[1]).glob('PEAudit_*.v'):
    source = re.sub(r"(?<![\w.'])(?:LG|CaseLogic)(?![\w'])", 'HLG', path.read_text())
    source = source.replace('HelloGlibcJoin AuditRuntime.', 'HelloGlibcJoin InterpRuntime.')
    # Query-local aliases must not become global fallback aliases for unrelated
    # library files while the flatten stage builds its namespace index.
    names = re.findall(r'^Module (\w+) := (?!Logic\b)', source, re.M)
    for name in names:
        source = re.sub(r"(?<![\w.'])" + name + r"(?![\w'])",
                        path.stem + '_' + name, source)
    # Separate query files intentionally reuse regression names. They are not
    # library exports and must not change the library's duplicate-name gate.
    locals = re.findall(r'^\s*(?:Lemma|Theorem|Corollary|Definition)\s+(\w+)', source, re.M)
    renames[path.name] = {path.stem + '_' + name: name for name in locals}
    for renamed, name in renames[path.name].items():
        source = re.sub(r"(?<![\w.'])" + name + r"(?![\w'])", renamed, source)
    path.write_text(source)
Path(sys.argv[2]).write_text(json.dumps(renames))
PY
"$here/../apply.sh" "$tmp/source" "$tmp/flat"
python3 - "$tmp/flat" "$tmp/renames.json" "$here/layouts/original" "$out" <<'PY'
from pathlib import Path
import json
import re
import sys
flat, mapping, original, out = map(Path, sys.argv[1:])
renames = json.loads(mapping.read_text())
for file in original.glob('*.v'):
    name = 'PEAudit_' + file.stem.replace('-', '_') + '.v'
    source = (flat / name).read_text()
    for renamed, local in renames[name].items():
        source = re.sub(r'\b' + renamed + r'\b', local, source)
    (out / file.name).write_text(source)
contracts = json.loads((original.parent.parent / 'audit-contracts.json').read_text())
contracts['m3']['hello_never_panics'] = []
(out / 'contracts.json').write_text(json.dumps(contracts, indent=2) + '\n')
PY
printf '%s\n' '{"Fix.R": "AuditRuntime", "Glibc.Fix.R": "AuditRuntime"}' >"$out/assumption-aliases.json"
