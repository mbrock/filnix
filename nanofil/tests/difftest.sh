#!/usr/bin/env bash
# Differential test: for each QBE file, compare the interpreter's results on
# its "# run:" lines with native code from three compilations:
#   original  real qbe on the file
#   printed   real qbe on nanofil's printed version of the file
#   nanofil   nanofil's own backend
#
#   difftest.sh FILE...    (needs tpl, qbe and cc on PATH, or TPL/QBE/CC set)
#   VARIANTS="nanofil" difftest.sh FILE...    to run a subset
#
# A Fil-C module (one that uses class p) has no qbe counterpart. It is
# compiled by nanofil only, linked with a clang-built Fil-C harness
# (FILCC, a filcc clang), and each run executes in its own process: a
# Fil-C safety panic is the native form of the interpreter's trap.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
tpl=${TPL:-tpl}
qbe=${QBE:-qbe}
cc=${CC:-cc}
filcc=${FILCC:-}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

status=0
for f in "$@"; do
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  d="$work/$(basename "$f" .ssa)"
  mkdir -p "$d"
  (cd "$src" && "$tpl" -q main.pl -- difftest "$f" "$d" </dev/null)
  if [ "$(cat "$d/mode")" = filc ]; then
    if [ -z "$filcc" ]; then echo "$f: Fil-C module, set FILCC" >&2; exit 2; fi
    (cd "$src" && "$tpl" -q main.pl -- compile "$f" </dev/null) >"$d/filc.s"
    as -o "$d/filc.o" "$d/filc.s"
    "$filcc" -O1 -o "$d/filc" "$d/harness.c" "$d/filc.o"
    n=$(wc -l <"$d/expected.txt")
    : >"$d/filc.txt"
    for ((i = 0; i < n; i++)); do
      if bash -c '"$@" >"$0.out" 2>"$0.err"; exit $?' "$d/run" "$d/filc" "$i" 2>/dev/null; then
        cat "$d/run.out" >>"$d/filc.txt"
      elif grep -q 'filc safety error' "$d/run.err"; then
        echo "$(cat "$d/run.out")trap" >>"$d/filc.txt"
      else
        echo "$(cat "$d/run.out")crash: $(head -c 200 "$d/run.err" | tr '\n' ' ')" >>"$d/filc.txt"
      fi
    done
    if ! diff -u "$d/expected.txt" "$d/filc.txt" >"$d/filc.diff"; then
      echo "MISMATCH $f (filc):"
      cat "$d/filc.diff"
      status=1
    fi
    continue
  fi
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
