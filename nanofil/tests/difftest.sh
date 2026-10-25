#!/usr/bin/env bash
# Differential test: for each IR file (src/ir_text.pl), compare the
# interpreter's results on its run(Fn, Args) facts with the native code
# nanofil's own backend makes of it.
#
#   difftest.sh FILE...    (needs cc on PATH, or CC set; see bin/nanofil for the Prolog host)
#   NANOFIL_OPT=-O difftest.sh FILE...        nanofil runs its middle end;
#     the interpreter checks each run before and after it (main.pl)
#
# A plain module is compiled to ordinary x86-64 and linked with a cc
# harness. A Fil-C module (one that uses class p) is linked with a
# clang-built Fil-C harness (FILCC, a filcc clang), and each run executes
# in its own process: a Fil-C safety panic is the native form of the
# interpreter's trap. These executables are non-PIE so globals also test
# bounds arithmetic at low addresses; filc/run-c.sh covers PIE executables.
#
# A C file is preprocessed and lowered by nanofil (cc-ir), and its
# "// run: $fn arg..." comments become run facts. Besides nanofil's own
# code it is also compiled from source by FILCC (variant clang), so the
# interpreter, nanofil and clang must all agree.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
nanofil="$here/../bin/nanofil"
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
    f="$d/c.ir"
    (cd "$src" && "$nanofil" cc-ir "$csrc" </dev/null) >"$f"
    awk '/^\/\/ run: \$/ { sub(/^\/\/ run: \$/, ""); fn = $1; $1 = ""
         sub(/^ +/, ""); gsub(/ +/, ", "); printf "run(\x27%s\x27, [%s]).\n", fn, $0 }' \
      "$csrc" >>"$f"
  fi
  (cd "$src" && "$nanofil" ${NANOFIL_OPT:-} difftest "$f" "$d" </dev/null)
  if [ "$(cat "$d/mode")" = filc ]; then
    if [ -z "$filcc" ]; then echo "$f: Fil-C module, set FILCC" >&2; exit 2; fi
    (cd "$src" && "$nanofil" ${NANOFIL_OPT:-} compile "$f" </dev/null) >"$d/filc.s"
    as -o "$d/filc.o" "$d/filc.s"
    "$filcc" -O1 -fno-pie -no-pie -o "$d/filc" "$d/harness.c" "$d/filc.o"
    variants=filc
    if [ -n "$csrc" ]; then
      "$filcc" -O1 -fno-pie -no-pie -o "$d/clang" "$d/harness.c" "$csrc"
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
  (cd "$src" && "$nanofil" ${NANOFIL_OPT:-} compile "$f" </dev/null) >"$d/nanofil.s"
  "$cc" -o "$d/nanofil" "$d/harness.c" "$d/nanofil.s"
  "$d/nanofil" >"$d/nanofil.txt"
  if ! diff -u "$d/expected.txt" "$d/nanofil.txt" >"$d/nanofil.diff"; then
    echo "MISMATCH $f:"
    cat "$d/nanofil.diff"
    status=1
  fi
done
exit $status
