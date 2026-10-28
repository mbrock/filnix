#!/usr/bin/env bash
# The access-check boundaries of docs/perf.md item 6a:
# tests/c/checks/bounds.c built by nanofil -O (NANOFIL_OPT added), whose
# checks of at most 16 bytes have no borrow test, and with
# --registers=stack, the reference selection that keeps it, and by
# FILCC -O1. Each case, size and direction must give the same stdout,
# stderr (pids and addresses aside) and status under both nanofil
# builds, and trap or not as the filcc build does. The -O build must
# have dropped the borrow test, so the comparison is not of two
# reference builds.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
filcc=${FILCC:?set FILCC to a filcc clang}
src=$here/c/checks/bounds.c
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
build() { # build DIR OPTIONS...
  local d=$work/$1; shift; mkdir -p "$d"
  (cd "$here/../src" && ../bin/nanofil ${NANOFIL_OPT:-} "$@" cc "$src" </dev/null) >"$d/t.s"
  as -o "$d/t.o" "$d/t.s"
  "$filcc" -o "$d/bounds" "$d/t.o"
}
build opt -O
build ref -O --registers=stack
mkdir -p "$work/filcc"
"$filcc" -O1 -w -o "$work/filcc/bounds" "$src"
# Upper - Size followed directly by the upper comparison: no borrow test.
borrowless() { grep -A1 -E '^\s*subq\s+\$(1|2|4|8|10), %rdx' "$1" | grep -c -E '^\s*cmpq\s+%rdx, %rax' || true; }
opt_n=$(borrowless "$work/opt/t.s") ref_n=$(borrowless "$work/ref/t.s")
if [[ ${NANOFIL_REGISTERS:-} != stack ]]; then
  [[ $opt_n -ge 5 ]] || { echo "checks: only $opt_n borrowless checks in the -O build" >&2; exit 1; }
fi
[[ $ref_n -eq 0 ]] || { echo "checks: $ref_n borrowless checks in the reference build" >&2; exit 1; }
run() { # run DIR CASE SIZE OP: stdout, normalized stderr and status in DIR/out
  local d=$work/$1
  set +e
  (cd "$d" && ./bounds "$2" "$3" "$4" >stdout 2>stderr) 2>/dev/null
  local rc=$?
  set -e
  sed -E 's/0x[0-9a-f]+/0x?/g; s/^\[[0-9]+\]/[pid]/' "$d/stderr" >"$d/out"
  cat "$d/stdout" >>"$d/out"
  echo "exit $rc" >>"$d/out"
  if grep -q 'filc safety error\|filc panic' "$d/stderr"; then echo trap; else echo "exit $rc"; fi
}
status=0 n=0
for c in lower last straddle end below freed null; do
  for size in 1 2 4 8 10; do
    for op in read write; do
      a=$(run opt "$c" "$size" "$op"); run ref "$c" "$size" "$op" >/dev/null
      f=$(run filcc "$c" "$size" "$op")
      case $c in lower|last) want="exit 0" ;; *) want=trap ;; esac
      if ! diff -u "$work/ref/out" "$work/opt/out" >"$work/diff"; then
        echo "MISMATCH $c $size $op (-O against reference):"; cat "$work/diff"; status=1
      elif [[ $a != "$f" || $a != "$want" ]]; then
        echo "MISMATCH $c $size $op: nanofil $a, filcc $f, expected $want"; status=1
      fi
      n=$((n + 1))
    done
  done
done
echo "checks: $n cases compared, $opt_n borrowless checks"
exit $status
