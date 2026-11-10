#!/usr/bin/env bash
# The extracted middle end against promote.pl and copy.pl
# (docs/gallina-backend.md, M5b): for each IR or C file, `nanofil
# promote-terms` prints the module, what promote.pl makes of it and
# what copy.pl makes of that, as terms; the extracted backend
# (BACKEND, built by make in rocq/backend) runs each pass on the
# term before it and must get the term after it. A file nanofil
# refuses is skipped. Fails if any item differs.
#
#   BACKEND=.../nanofil-backend promote.sh FILE...
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../../../src"
nanofil="$here/../../../bin/nanofil"
backend=${BACKEND:-$here/../nanofil-backend}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

status=0
for f in "$@"; do
  t0=$SECONDS
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  echo "@@nanofil-backend $(date -u +%FT%TZ) start promote file=$f"
  if ! (cd "$src" && "$nanofil" promote-terms "$f" </dev/null) >"$work/terms" 2>"$work/err"; then
    echo "skip $f: $(head -c 100 "$work/err" | head -1)"
    continue
  fi
  if ! "$backend" promote <"$work/terms" >"$work/out" 2>"$work/err"; then
    echo "DIFFER $f: $(tr '\n' ' ' <"$work/out")"
    head -c 4000 "$work/err"
    status=1
  else
    echo "same $f: $(tr '\n' ' ' <"$work/out")"
  fi
  echo "@@nanofil-backend $(date -u +%FT%TZ) done promote file=$f seconds=$((SECONDS - t0))"
done
exit $status
