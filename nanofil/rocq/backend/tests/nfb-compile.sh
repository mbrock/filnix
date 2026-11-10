#!/usr/bin/env bash
# The standalone compiler's NFB input against its IR text input
# (docs/nfb.md): for each IR file, `nanofil encode-input` writes the
# module's NFB, and the extracted backend (BACKEND, built by make in
# rocq/backend) must print the very same assembly, with the same exit
# status, from `compile-nfb FILE.nfb` as from `compile FILE.ir`. A file
# nanofil refuses to encode is skipped. Fails if any output differs.
#
#   BACKEND=.../nanofil-backend nfb-compile.sh FILE.ir...
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nanofil="$here/../../../bin/nanofil"
backend=${BACKEND:-$here/../nanofil-backend}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

status=0
for f in "$@"; do
  t0=$SECONDS
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  echo "@@nanofil-backend $(date -u +%FT%TZ) start nfb-compile file=$f"
  if ! "$nanofil" encode-input "$f" "$work/m.nfb" </dev/null >/dev/null 2>"$work/err"; then
    echo "skip $f: $(head -c 100 "$work/err" | head -1)"
    continue
  fi
  "$backend" compile "$f" >"$work/text.s" 2>/dev/null
  a=$?
  "$backend" compile-nfb "$work/m.nfb" >"$work/nfb.s" 2>/dev/null
  b=$?
  if [ "$a" != "$b" ] || ! cmp -s "$work/text.s" "$work/nfb.s"; then
    echo "DIFFER $f: exit $a from the text, $b from NFB"
    cmp "$work/text.s" "$work/nfb.s" | head -1
    status=1
  else
    echo "same $f: exit $a, $(wc -c <"$work/nfb.s") bytes"
  fi
  echo "@@nanofil-backend $(date -u +%FT%TZ) done nfb-compile file=$f seconds=$((SECONDS - t0))"
done
exit $status
