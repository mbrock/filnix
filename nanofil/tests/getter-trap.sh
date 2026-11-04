#!/usr/bin/env bash
# Facts kept across repeated getters (docs/forward.md, Getters) keep
# every trap: tests/c/getter/main.c is built by nanofil -O with
# reference checks and with --checks=getter and extended, linked with
# lib.c built by filcc (ifuncs whose resolvers free and store), and run
# with 1 (the first getter frees), 2 (a repeated external getter frees)
# and 0 (facts kept across a local repeated getter). stdout, the exit status and the whole stderr
# (addresses and the pid masked) must agree with reference checks, the
# reference build must trap, and the getter build must have fewer jumps
# to check failures than combined, or the comparison would show nothing.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
src=$here/c/getter
"$filcc" -c -o "$work/lib.o" "$src/lib.c"
for c in reference combined getter extended; do
  d=$work/$c; mkdir -p "$d"
  (cd "$here/../src" && ../bin/nanofil -O --checks=$c --share=none cc "$src/main.c" </dev/null) >"$d/main.s"
  as -o "$d/main.o" "$d/main.s"
  "$filcc" -o "$d/getter" "$d/main.o" "$work/lib.o"
  : >"$d/out"
  for m in 1 2 0; do
    set +e
    "$d/getter" $m >>"$d/out" 2>"$d/err"
    echo "exit $?" >>"$d/out"
    set -e
    sed -E 's/0x[0-9a-f]+/0x?/g; s/^\[[0-9]+\]/[pid]/' "$d/err" >>"$d/out"
  done
done
tests() { grep -cE '^\s*j[a-z]+\s+\.L.*\.\.fail\.' "$1" || true; }
status=0
if ! grep -q 'filc safety error' "$work/reference/out"; then
  echo "getter: the reference build does not trap"; status=1
elif (( $(grep -c 'filc safety error' "$work/reference/out") < 2 )); then
  echo "getter: the reference build does not trap in both runs"; status=1
elif (( $(tests "$work/getter/main.s") >= $(tests "$work/combined/main.s") )); then
  echo "getter: no fact kept across a getter in the getter build"; status=1
fi
for c in getter extended; do
  if diff -u "$work/reference/out" "$work/$c/out"; then
    echo "getter $c: ok ($(grep -m1 'filc safety error' "$work/$c/out"))"
  else
    status=1
  fi
done
exit $status
