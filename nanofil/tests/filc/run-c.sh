#!/usr/bin/env bash
# Link NAME.ssa (compiled by nanofil) with NAME.c (clang-built Fil-C),
# run case i of NAME.expected in its own process for every line i, and
# compare. A Fil-C safety panic prints as "trap".
#
#   run-c.sh NAME...    (needs TPL and FILCC)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../../src"
tpl=${TPL:-tpl}
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
status=0
for name in "$@"; do
  d="$work/$name"
  mkdir -p "$d"
  (cd "$src" && "$tpl" -q main.pl -- compile "$here/$name.ssa" </dev/null) >"$d/n.s"
  as -o "$d/n.o" "$d/n.s"
  "$filcc" -O1 -o "$d/t" "$here/$name.c" "$d/n.o"
  n=$(wc -l <"$here/$name.expected")
  : >"$d/out.txt"
  for ((i = 0; i < n; i++)); do
    if bash -c '"$@" >"$0.out" 2>"$0.err"; exit $?' "$d/run" ${RUN_ENV:+env $RUN_ENV} "$d/t" "$i" 2>/dev/null; then
      cat "$d/run.out" >>"$d/out.txt"
    elif grep -q 'filc safety error' "$d/run.err"; then
      echo "$(cat "$d/run.out")trap" >>"$d/out.txt"
    else
      echo "$(cat "$d/run.out")crash: $(head -c 300 "$d/run.err" | tr '\n' ' ')" >>"$d/out.txt"
    fi
  done
  if diff -u "$here/$name.expected" "$d/out.txt"; then
    echo "$name: $n cases ok"
  else
    status=1
  fi
done
exit $status
