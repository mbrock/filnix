#!/usr/bin/env bash
# Whole programs: each tests/c/prog/NAME.c is built by nanofil (main
# included, linked by FILCC) and by FILCC -O1 alone, and both runs must
# agree on stdout, stderr and exit status. A Fil-C safety panic counts as
# "trap" (its message names different functions in the two builds). An
# "// args: ..." line gives the arguments.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
tpl=${TPL:-tpl}
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
status=0
n=0
run() {
  local exe=$1 out=$2
  shift 2
  set +e
  # The inner shell reports a fatal signal, so keep its stderr quiet.
  bash -c '"$@" >"$0.stdout" 2>"$0.stderr"; exit $?' "$out" ${RUN_ENV:-} "$exe" "$@" 2>/dev/null
  local rc=$?
  set -e
  if grep -q 'filc safety error' "$out.stderr"; then
    echo trap >"$out.stderr"
    rc=trap
  fi
  echo "exit $rc" >"$out.status"
}
for f in "$here"/c/prog/*.c; do
  name=$(basename "$f" .c)
  d="$work/$name"
  mkdir -p "$d"
  read -r -a args <<<"$(sed -n 's|^// args: ||p' "$f")"
  "$filcc" -E -o "$d/p.i" "$f"
  (cd "$src" && "$tpl" -q main.pl -- cc "$d/p.i" </dev/null) >"$d/n.s"
  as -o "$d/n.o" "$d/n.s"
  "$filcc" -o "$d/nanofil" "$d/n.o"
  "$filcc" -O1 -w -o "$d/clang" "$f"
  run "$d/nanofil" "$d/n" "${args[@]}"
  run "$d/clang" "$d/c" "${args[@]}"
  for part in stdout stderr status; do
    if ! diff -u "$d/c.$part" "$d/n.$part" >"$d/$part.diff"; then
      echo "MISMATCH $f ($part):"; cat "$d/$part.diff"; status=1
    fi
  done
  n=$((n + 1))
done
echo "progtest: $n programs compared"
exit $status
