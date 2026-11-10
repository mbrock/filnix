#!/usr/bin/env bash
# The Gallina NFB writer and reader against nfb.pl (docs/nfb.md): for
# each IR or C file, `nanofil nfb-terms` writes the NFB of its module,
# and of a Fil-C module's checked module, and prints each module as a
# term. The extracted backend (BACKEND, built by make in rocq/backend)
# reads each term as decode_module does; Nfb.v's encode must write the
# very words nfb.pl wrote, and its decode must read those words back
# as the same module. A file nanofil refuses is skipped. Fails if any
# word or module differs.
#
#   BACKEND=.../nanofil-backend nfb.sh FILE...
#   NANOFIL_OPT=-O nfb.sh FILE...     after the middle end
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
  echo "@@nanofil-backend $(date -u +%FT%TZ) start nfb file=$f"
  # shellcheck disable=SC2086
  if ! (cd "$src" && "$nanofil" ${NANOFIL_OPT:-} nfb-terms "$f" "$work/m" </dev/null) >"$work/terms" 2>"$work/err"; then
    echo "skip $f: $(head -c 100 "$work/err" | head -1)"
    continue
  fi
  if ! "$backend" nfb "$work/m" <"$work/terms" >"$work/out" 2>"$work/err"; then
    echo "DIFFER $f:"
    cat "$work/out"
    head -c 4000 "$work/err"
    status=1
  else
    echo "same $f: $(tr '\n' ' ' <"$work/out")"
  fi
  rm -f "$work"/m.*.nfb
  echo "@@nanofil-backend $(date -u +%FT%TZ) done nfb file=$f seconds=$((SECONDS - t0))"
done
exit $status
