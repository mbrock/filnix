#!/usr/bin/env bash
# The failing small copies of docs/perf.md item 7a: tests/c/memcpy/traps.c
# built by nanofil with the inline filter (-O, NANOFIL_OPT added) and
# with --memcpy=call, and by FILCC -O1. Each case at each size must give
# the same stdout, stderr (pids and addresses aside) and status under
# both nanofil builds, and trap or not as the filcc build does. With -O
# the filter must be present, so a case that silently kept the call
# cannot pass for a case the filter sent to the call.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
filcc=${FILCC:?set FILCC to a filcc clang}
src=$here/c/memcpy/traps.c
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
build() { # build DIR OPTIONS...
  local d=$work/$1; shift; mkdir -p "$d"
  (cd "$here/../src" && ../bin/nanofil ${NANOFIL_OPT:-} "$@" cc "$src" </dev/null) >"$d/t.s"
  as -o "$d/t.o" "$d/t.s"
  "$filcc" -o "$d/traps" "$d/t.o"
}
build inline -O
build call -O --memcpy=call
mkdir -p "$work/filcc"
"$filcc" -O1 -w -o "$work/filcc/traps" "$src"
filters=$(grep -c '\.copied:$' "$work/inline/t.s" || true)
[[ $filters -ge 54 ]] || { echo "memcpy: only $filters filters in the -O build" >&2; exit 1; }
run() { # run DIR CASE N: stdout, normalized stderr and status in DIR/out
  local d=$work/$1
  set +e
  (cd "$d" && ./traps "$2" "$3" >stdout 2>stderr) 2>/dev/null
  local rc=$?
  set -e
  sed -E 's/0x[0-9a-f]+/0x?/g; s/^\[[0-9]+\]/[pid]/' "$d/stderr" >"$d/out"
  cat "$d/stdout" >>"$d/out"
  echo "exit $rc" >>"$d/out"
  # filcc's inline check reports a source below lower as a failed
  # assertion in filc_optimized_access_check_fail: a panic all the same.
  if grep -q 'filc safety error\|filc panic' "$d/stderr"; then echo trap; else echo "exit $rc"; fi
}
status=0 n=0
for c in dst-aux src-aux readonly freed-dst freed-src dst-end dst-below \
         src-end src-below null-dst null-src function empty result; do
  for size in 1 8 9 16; do
    a=$(run inline "$c" "$size"); b=$(run call "$c" "$size"); f=$(run filcc "$c" "$size")
    if ! diff -u "$work/call/out" "$work/inline/out" >"$work/diff"; then
      echo "MISMATCH $c $size (inline against call):"; cat "$work/diff"; status=1
    elif [[ $a != "$f" ]]; then
      echo "MISMATCH $c $size: nanofil $a, filcc $f"; status=1
    fi
    n=$((n + 1))
  done
done
echo "memcpy: $n cases compared, $filters filters"
exit $status
