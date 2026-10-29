#!/usr/bin/env bash
# Check renewal keeps each trap's text (docs/m7.md, round 4): every
# tests/c/prog/renew-*.c is built by nanofil -O with reference checks and
# with --checks=renew, and both runs must agree on stdout, the exit
# status and the whole stderr (the safety error, its pointer's state,
# expected bytes and origins) with addresses and the pid masked. The
# renew build must have fewer full checks (renewals), or the comparison
# would show nothing.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
status=0
for f in "$here"/c/prog/renew-*.c; do
  name=$(basename "$f" .c)
  read -r -a args <<<"$(sed -n 's|^// args: ||p' "$f")"
  for c in reference renew; do
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
  if (( $(full "$work/renew/$name.s") >= $(full "$work/reference/$name.s") )); then
    echo "$name: no renewal in the renew build"; status=1
  elif ! grep -q 'filc safety error' "$work/reference/$name.out"; then
    echo "$name: the reference build does not trap"; status=1
  elif diff -u "$work/reference/$name.out" "$work/renew/$name.out"; then
    echo "$name: ok ($(grep -m1 'filc safety error' "$work/renew/$name.out"))"
  else
    status=1
  fi
done
exit $status
