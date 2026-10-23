#!/usr/bin/env bash
# Differential test: for each QBE file, compare the interpreter's results on
# its "# run:" lines with native code from three compilations:
#   original  real qbe on the file
#   printed   real qbe on nanofil's printed version of the file
#   nanofil   nanofil's own backend
#
#   difftest.sh FILE...    (needs tpl, qbe and cc on PATH, or TPL/QBE/CC set)
#   VARIANTS="nanofil" difftest.sh FILE...    to run a subset
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
  for variant in ${VARIANTS:-original printed nanofil}; do
    case $variant in
      original) "$qbe" -o "$d/$variant.s" "$f" ;;
      printed) "$qbe" -o "$d/$variant.s" "$d/printed.ssa" ;;
      nanofil) (cd "$src" && "$tpl" -q main.pl -- compile "$f" </dev/null) >"$d/$variant.s" ;;
    esac
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
