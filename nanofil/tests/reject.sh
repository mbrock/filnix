#!/usr/bin/env bash
# Rejection tests: each tests/c/reject/NAME.c starts with "// error: TEXT"
# and nanofil must refuse it with a message containing TEXT. Needs TPL and
# FILCC (whose -E is the preprocessor for now).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
tpl=${TPL:-tpl}
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
status=0
n=0
for f in "$here"/c/reject/*.c; do
  want=$(sed -n '1s|^// error: ||p' "$f")
  "$filcc" -E -o "$work/t.i" "$f"
  if (cd "$src" && "$tpl" -q main.pl -- cc-ir "$work/t.i" </dev/null) >"$work/out" 2>"$work/err"; then
    echo "ACCEPTED $f (wanted: $want)"; status=1
  elif ! grep -qF -- "$want" "$work/err"; then
    echo "WRONG ERROR $f: $(cat "$work/err") (wanted: $want)"; status=1
  fi
  n=$((n + 1))
done
echo "reject: $n cases checked"
exit $status
