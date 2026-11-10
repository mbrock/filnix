#!/usr/bin/env bash
# The extracted pizlonation against pizlonate.pl
# (docs/gallina-backend.md, M4): for each IR or C file, `nanofil
# pizlonate-terms` prints the module and then its pizlonation, as
# terms; the extracted backend (BACKEND, built by make in
# rocq/backend) pizlonates the first again and must get the second.
# A plain module is pizlonated too: it gets its polls. A file nanofil
# refuses is skipped. Fails if any item differs.
#
#   BACKEND=.../nanofil-backend pizlonate.sh FILE...
#   NANOFIL_OPT=-O pizlonate.sh FILE...     after the middle end
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
  tag="opt=${NANOFIL_OPT:-plain} file=$f"
  echo "@@nanofil-backend $(date -u +%FT%TZ) start pizlonate $tag"
  if ! (cd "$src" && "$nanofil" ${NANOFIL_OPT:-} pizlonate-terms "$f" </dev/null) >"$work/terms" 2>"$work/err"; then
    echo "skip $f: $(head -c 100 "$work/err" | head -1)"
    continue
  fi
  if ! "$backend" pizlonate <"$work/terms" >"$work/out" 2>"$work/err"; then
    echo "DIFFER $f: $(cat "$work/out")"
    head -c 4000 "$work/err"
    status=1
  else
    echo "same $f: $(cat "$work/out")"
  fi
  echo "@@nanofil-backend $(date -u +%FT%TZ) done pizlonate $tag seconds=$((SECONDS - t0))"
done
exit $status
