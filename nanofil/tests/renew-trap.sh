#!/usr/bin/env bash
# Check renewal and range guards keep each trap's text (docs/m7.md,
# rounds 4 and 5): every tests/c/prog/renew-*.c and guard-*.c is built by
# nanofil -O with reference checks and with --checks=renew or guard, and
# both runs must agree on stdout, the exit
# status and the whole stderr (the safety error, its pointer's state,
# expected bytes and origins) with addresses and the pid masked. The
# renew build must have fewer full checks (renewals), and the guard
# build a guarded access, or the comparison would show nothing.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
status=0
for f in "$here"/c/prog/renew-*.c "$here"/c/prog/guard-*.c; do
  name=$(basename "$f" .c)
  mode=${name%%-*}
  read -r -a args <<<"$(sed -n 's|^// args: ||p' "$f")"
  for c in reference $mode; do
    # The same file name in both, since origins name the executable.
    d=$work/$c; mkdir -p "$d"
    (cd "$here/../src" && ../bin/nanofil -O --checks=$c cc "$f" </dev/null) >"$d/$name.s"
    as -o "$d/$name.o" "$d/$name.s"
    "$filcc" -o "$d/$name" "$d/$name.o"
    set +e
    bash -c '"$@" >"$0.out" 2>"$0.err"; exit $?' "$d/$name" ${RUN_ENV:-} "$d/$name" "${args[@]}" 2>/dev/null
    echo "exit $?" >>"$d/$name.out"
    set -e
    sed -E 's/0x[0-9a-f]+/0x?/g; s/^\[[0-9]+\]/[pid]/' "$d/$name.err" >>"$d/$name.out"
  done
  full() { grep -cE '^\s*jz\s+\.L.*\.\.fail\.' "$1" || true; }
  # A guarded access's full check is out of line, after a .full label.
  guarded() { grep -cE '\.full:$' "$1" || true; }
  if [[ $mode == guard ]] && (( $(guarded "$work/guard/$name.s") == 0 )); then
    echo "$name: no guarded access in the guard build"; status=1
  elif [[ $mode == renew ]] && (( $(full "$work/renew/$name.s") >= $(full "$work/reference/$name.s") )); then
    echo "$name: no renewal in the $mode build"; status=1
  elif ! grep -q 'filc safety error' "$work/reference/$name.out"; then
    echo "$name: the reference build does not trap"; status=1
  elif diff -u "$work/reference/$name.out" "$work/$mode/$name.out"; then
    echo "$name: ok ($(grep -m1 'filc safety error' "$work/$mode/$name.out"))"
  else
    status=1
  fi
done
exit $status
