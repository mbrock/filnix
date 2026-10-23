#!/usr/bin/env bash
# Differential test: for each QBE file, compare the interpreter's results on
# its "# run:" lines with native code from three compilations:
#   original  real qbe on the file
#   printed   real qbe on nanofil's printed version of the file
#   nanofil   nanofil's own backend
#
#   difftest.sh FILE...    (needs tpl, qbe and cc on PATH, or TPL/QBE/CC set)
#   VARIANTS="nanofil" difftest.sh FILE...    to run a subset
#   NANOFIL_OPT=-O difftest.sh FILE...        nanofil runs its middle end;
#     the interpreter checks each run before and after it (main.pl)
#
# A Fil-C module (one that uses class p) has no qbe counterpart. It is
# compiled by nanofil only, linked with a clang-built Fil-C harness
# (FILCC, a filcc clang), and each run executes in its own process: a
# Fil-C safety panic is the native form of the interpreter's trap.
#
# A C file is preprocessed and lowered by nanofil (cc-ir), and its
# "// run: $fn arg..." comments become run lines. Besides nanofil's own
# code it is also compiled from source by FILCC (variant clang), so the
# interpreter, nanofil and clang must all agree.
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
  b=$(basename "$f"); d="$work/${b%.*}"
  mkdir -p "$d"
  csrc=
  if [[ $f == *.c ]]; then
    if [ -z "$filcc" ]; then echo "$f: C file, set FILCC" >&2; exit 2; fi
    csrc=$f
    f="$d/c.ssa"
    (cd "$src" && "$tpl" -q main.pl -- cc-ir "$csrc" </dev/null) >"$f"
    sed -n 's|^// run: |# run: |p' "$csrc" >>"$f"
  fi
  (cd "$src" && "$tpl" -q main.pl -- ${NANOFIL_OPT:-} difftest "$f" "$d" </dev/null)
  if [ "$(cat "$d/mode")" = filc ]; then
    if [ -z "$filcc" ]; then echo "$f: Fil-C module, set FILCC" >&2; exit 2; fi
    (cd "$src" && "$tpl" -q main.pl -- ${NANOFIL_OPT:-} compile "$f" </dev/null) >"$d/filc.s"
    as -o "$d/filc.o" "$d/filc.s"
    "$filcc" -O1 -o "$d/filc" "$d/harness.c" "$d/filc.o"
    variants=filc
    if [ -n "$csrc" ]; then
      "$filcc" -O1 -o "$d/clang" "$d/harness.c" "$csrc"
      variants="filc clang"
    fi
    n=$(wc -l <"$d/expected.txt")
    for v in $variants; do
      : >"$d/$v.txt"
      for ((i = 0; i < n; i++)); do
        if bash -c '"$@" >"$0.out" 2>"$0.err"; exit $?' "$d/run" "$d/$v" "$i" 2>/dev/null; then
          cat "$d/run.out" >>"$d/$v.txt"
        elif grep -q 'filc safety error' "$d/run.err"; then
          echo "$(cat "$d/run.out")trap" >>"$d/$v.txt"
        else
          echo "$(cat "$d/run.out")crash: $(head -c 200 "$d/run.err" | tr '\n' ' ')" >>"$d/$v.txt"
        fi
      done
      if ! diff -u "$d/expected.txt" "$d/$v.txt" >"$d/$v.diff"; then
        echo "MISMATCH ${csrc:-$f} ($v):"
        cat "$d/$v.diff"
        status=1
      fi
    done
    continue
  fi
  for variant in ${VARIANTS:-original printed nanofil}; do
    case $variant in
      original) "$qbe" -o "$d/$variant.s" "$f" ;;
      printed) "$qbe" -o "$d/$variant.s" "$d/printed.ssa" ;;
      nanofil) (cd "$src" && "$tpl" -q main.pl -- ${NANOFIL_OPT:-} compile "$f" </dev/null) >"$d/$variant.s" ;;
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
