#!/usr/bin/env bash
# Shared check parts (docs/perf.md item 17) keep every trap: each
# tests/c/prog/share-*.c is built by nanofil -O, by nanofil -O
# --share=upper and by filcc -O2 without check scheduling
# (-filc-optimize-checks=false), whose traps stand where nanofil's do:
# -O2's scheduler merges checks and reports "cannot access" for a merged
# read (docs/perf.md item 16). All three must agree on stdout and the
# exit status, the share build's first safety error must be filcc's,
# and its whole stderr (the error, the pointer's state, origins) the -O
# build's, with addresses and the pid masked. The share build must have
# fewer null tests or upper loads than the -O build, or the comparison
# would show nothing.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
status=0
for f in "$here"/c/prog/share-*.c; do
  name=$(basename "$f" .c)
  read -r -a args <<<"$(sed -n 's|^// args: ||p' "$f")"
  for c in none upper filcc; do
    # The same file name in all, since origins name the executable.
    d=$work/$c; mkdir -p "$d"
    if [[ $c == filcc ]]; then
      "$filcc" -O2 -mllvm -filc-optimize-checks=false -o "$d/$name" "$f"
    else
      (cd "$here/../src" && ../bin/nanofil -O --share=$c cc "$f" </dev/null) >"$d/$name.s"
      as -o "$d/$name.o" "$d/$name.s"
      "$filcc" -o "$d/$name" "$d/$name.o"
    fi
    set +e
    bash -c '"$@" >"$0.out" 2>"$0.err"; exit $?' "$d/$name" "$d/$name" "${args[@]}" 2>/dev/null
    echo "exit $?" >>"$d/$name.out"
    set -e
    sed -E 's/0x[0-9a-f]+/0x?/g; s/^\[[0-9]+\]/[pid]/' "$d/$name.err" >"$d/$name.masked"
    grep -m1 'filc safety error' "$d/$name.masked" >"$d/$name.trap" || true
  done
  parts() { grep -cE '^\s*jz\s+\.L.*\.\.fail\.|-16\(%rcx\)' "$1" || true; }
  n=$work/none/$name u=$work/upper/$name c=$work/filcc/$name
  if (( $(parts "$u.s") >= $(parts "$n.s") )); then
    echo "$name: nothing shared in the share build"; status=1
  elif ! grep -q 'filc safety error' "$n.err"; then
    echo "$name: the -O build does not trap"; status=1
  elif ! cmp -s "$n.out" "$u.out" || ! cmp -s "$u.out" "$c.out"; then
    echo "$name: stdout or exit status differ"; diff "$n.out" "$u.out" || true; diff "$u.out" "$c.out" || true; status=1
  elif ! cmp -s "$u.trap" "$c.trap"; then
    echo "$name: share reports '$(cat "$u.trap")', filcc '$(cat "$c.trap")'"; status=1
  elif ! diff -u "$n.masked" "$u.masked"; then
    echo "$name: stderr differs from the -O build's"; status=1
  else
    echo "$name: ok ($(cat "$u.trap"))"
  fi
done
exit $status
