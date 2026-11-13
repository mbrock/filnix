#!/usr/bin/env bash
# Build just the generic Hello dependency closure and retain its audit.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
before=${1:?usage: hello-abstract.sh ORIGINAL_TREE NEW_OUTPUT_DIRECTORY}
out=${2:?usage: hello-abstract.sh ORIGINAL_TREE NEW_OUTPUT_DIRECTORY}
test ! -e "$out"
mkdir -p "$out"
out=$(cd "$out" && pwd)
if [ -n "${3:-}" ]; then
  ln -s "$(realpath "$3")" "$out/tree"
else
  PE_RUNTIME=abstract "$here/../apply.sh" "$before" "$out/tree"
fi
mkdir "$out/layout"
printf 'From Glibc Require Import HelloGlibcJoin.\nPrint Assumptions HelloGlibcJoin.hello_never_panics.\n' >"$out/layout/m3.v"
printf '%s\n' '{"Fix.R":"AuditRuntime","Glibc.Fix.R":"AuditRuntime"}' >"$out/layout/assumption-aliases.json"
python3 - "$here/audit-contracts.json" "$out/layout/contracts.json" <<'PY'
import json, sys
from pathlib import Path
contract = json.loads(Path(sys.argv[1]).read_text())['m3']['hello_never_panics']
Path(sys.argv[2]).write_text(json.dumps({'m3': {'hello_never_panics': contract}}))
PY
(
  cd "$out/tree"
  rocq makefile -R "$PE_MODEL" Nanofil -R . Glibc $(find . -name '*.v' | sort) -o Makefile
  make -j"${PE_JOBS:-8}" hello/HelloGlibcJoin.vo
)
python3 "$here/audit.py" "$out/tree" --layout "$out/layout" --output "$out/audit"
