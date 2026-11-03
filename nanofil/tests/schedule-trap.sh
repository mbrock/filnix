#!/usr/bin/env bash
# Scheduled checks (docs/schedule.md) trap as filcc -O2's check
# scheduler does: every tests/c/prog/schedule-*.c is built by nanofil -O
# with reference checks, by nanofil -O --checks=schedule and by filcc
# -O2. All three must agree on stdout and the exit status, and on
# whether a safety error is reported; the schedule build's first safety
# error line must equal filcc's. A program with an "// early" line must
# also trap differently from the reference build (its check was
# widened, so the comparison shows the earlier trap), and one without
# must report the reference build's safety error.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
status=0
for f in "$here"/c/prog/schedule-*.c; do
  name=$(basename "$f" .c)
  for c in reference schedule filcc; do
    # The same file name in all, since origins name the executable.
    d=$work/$c; mkdir -p "$d"
    if [[ $c == filcc ]]; then
      "$filcc" -O2 -o "$d/$name" "$f"
    else
      (cd "$here/../src" && ../bin/nanofil -O --checks=$c cc "$f" </dev/null) >"$d/$name.s"
      as -o "$d/$name.o" "$d/$name.s"
      "$filcc" -o "$d/$name" "$d/$name.o"
    fi
    set +e
    bash -c '"$0" >"$0.out" 2>"$0.err"' "$d/$name" 2>/dev/null
    echo "exit $?" >>"$d/$name.out"
    set -e
    grep -m1 'filc safety error' "$d/$name.err" >"$d/$name.trap" || true
  done
  r=$work/reference/$name s=$work/schedule/$name c=$work/filcc/$name
  if ! cmp -s "$r.out" "$s.out" || ! cmp -s "$s.out" "$c.out"; then
    echo "$name: stdout or exit status differ"; diff "$r.out" "$s.out" || true; diff "$s.out" "$c.out" || true; status=1
  elif ! cmp -s "$s.trap" "$c.trap"; then
    echo "$name: schedule reports '$(cat "$s.trap")', filcc -O2 '$(cat "$c.trap")'"; status=1
  elif [[ -s $r.trap && ! -s $s.trap || ! -s $r.trap && -s $s.trap ]]; then
    echo "$name: the reference build reports '$(cat "$r.trap")', schedule '$(cat "$s.trap")'"; status=1
  elif grep -q '^// early' "$f" && cmp -s "$r.trap" "$s.trap"; then
    echo "$name: no earlier trap in the schedule build ($(cat "$s.trap"))"; status=1
  elif ! grep -q '^// early' "$f" && ! cmp -s "$r.trap" "$s.trap"; then
    echo "$name: schedule reports '$(cat "$s.trap")', reference '$(cat "$r.trap")'"; status=1
  else
    echo "$name: ok ($(cat "$s.trap"))"
  fi
done
exit $status
