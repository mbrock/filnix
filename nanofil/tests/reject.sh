#!/usr/bin/env bash
# Rejection tests: each tests/c/reject/NAME.c starts with "// error: TEXT"
# and nanofil must refuse it with a message containing TEXT. Needs FILCC
# (for target macro and include-path discovery). A "// vectors" line
# turns on GNU vector types (NANOFIL_VECTORS=1), as in progtest.sh.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
nanofil="$here/../bin/nanofil"
export FILCC=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
status=0
n=0
for f in "$here"/c/reject/*.c; do
  want=$(sed -n '1s|^// error: ||p' "$f")
  vectors=; if grep -q '^// vectors' "$f"; then vectors=1; fi
  if (cd "$src" && NANOFIL_VECTORS=$vectors "$nanofil" cc-ir "$f" </dev/null) >"$work/out" 2>"$work/err"; then
    echo "ACCEPTED $f (wanted: $want)"; status=1
  elif ! grep -qF -- "$want" "$work/err"; then
    echo "WRONG ERROR $f: $(cat "$work/err") (wanted: $want)"; status=1
  fi
  n=$((n + 1))
done
echo "reject: $n cases checked"
exit $status
