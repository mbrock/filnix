#!/usr/bin/env bash
# Differential test: for each QBE file, compare the interpreter's results on
# its "# run:" lines with native code from real qbe, for both the original
# text and nanofil's printed version of it.
#
#   difftest.sh FILE...    (needs tpl, qbe and cc on PATH, or TPL/QBE/CC set)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
tpl=${TPL:-tpl}
qbe=${QBE:-qbe}
cc=${CC:-cc}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

status=0
for f in "$@"; do
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  d="$work/$(basename "$f" .ssa)"
  mkdir -p "$d"
  (cd "$src" && "$tpl" -q main.pl -- difftest "$f" "$d" </dev/null)
  for variant in original printed; do
    if [ $variant = original ]; then in=$f; else in=$d/printed.ssa; fi
    "$qbe" -o "$d/$variant.s" "$in"
    "$cc" -o "$d/$variant" "$d/harness.c" "$d/$variant.s"
    "$d/$variant" >"$d/$variant.txt"
    if ! diff -u "$d/expected.txt" "$d/$variant.txt" >"$d/$variant.diff"; then
      echo "MISMATCH $f ($variant):"
      cat "$d/$variant.diff"
      status=1
    fi
  done
done
exit $status
