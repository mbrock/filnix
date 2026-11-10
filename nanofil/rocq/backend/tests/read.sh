#!/usr/bin/env bash
# The IR text reader against Prolog's (docs/gallina-backend.md, M4).
# For each file, IrText.v's read_module must give the module
# `nanofil read-terms FILE.ir` prints, and nothing where Prolog
# throws. It fails if the reader reads a text differently (DIFFER),
# reads one Prolog refuses (ACCEPTED), reads one whose Prolog term
# the driver cannot read (UNREADABLE), or refuses one Prolog reads.
#
#   BACKEND=.../nanofil-backend read.sh FILE.ir...
#
# With --cases in place of the files, the texts are the adversarial
# cases read/cases.py writes: escapes, quotes, UTF-8, numbers,
# operators, comments and clause ends, most of them one form inside
# a context/2 clause. The reader may refuse a case Prolog reads, and
# then read/refused.txt must name it: the cases refused are to be
# exactly the ones listed, so a change of the reader that refuses
# more, or fewer, shows here. Prolog starts once for all the files.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../../../src"
nanofil="$here/../../../bin/nanofil"
backend=${BACKEND:-$here/../nanofil-backend}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

cases=
if [ "${1-}" = --cases ]; then
  cases=1
  python3 "$here/read/cases.py" "$work/cases"
  set -- "$work"/cases/*.ir
fi
files=()
for f in "$@"; do files+=("$(cd "$(dirname "$f")" && pwd)/$(basename "$f")"); done

(cd "$src" && "$nanofil" read-each "${files[@]}" </dev/null) >"$work/theirs" 2>"$work/their-err"
"$backend" read "${files[@]}" <"$work/theirs" >"$work/verdicts"

status=0
for k in same both-refuse refused DIFFER ACCEPTED UNREADABLE; do
  echo "$k $(grep -c "^$k " "$work/verdicts" || true)"
done
if grep -E '^(DIFFER|ACCEPTED|UNREADABLE) ' "$work/verdicts"; then status=1; fi
if [ -n "$cases" ]; then
  grep '^refused ' "$work/verdicts" | sed 's|.*/||; s|\.ir$||' | sort >"$work/refused"
  if ! diff <(sort "$here/read/refused.txt") "$work/refused" >"$work/diff"; then
    echo "the cases refused are not those of read/refused.txt (< listed, > refused now):"
    cat "$work/diff"
    status=1
  fi
elif grep '^refused ' "$work/verdicts"; then
  status=1
fi
exit $status
