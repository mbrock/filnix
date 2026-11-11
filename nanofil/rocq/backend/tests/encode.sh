#!/usr/bin/env bash
# The encoder against GNU as (Encode.v): for each IR file and each of
# compile, compile-promoted and compile-allocated, the extracted
# backend prints its assembly, GNU as assembles it, and tests/objdump.py
# prints the object; `nanofil-backend object...` must print the same
# text for the object Encode.v makes of the same lines: every section's
# bytes, every relocation and every symbol. A file the backend refuses
# or GNU as rejects is skipped, and so is a command the backend does
# not compile it with. Fails if any text differs or a line has no
# encoding.
#
#   encode.sh FILE.ir...
#   BACKEND=.../nanofil-backend AS=.../as COMMANDS="compile-allocated" encode.sh FILE.ir...
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
backend=${BACKEND:-$here/../nanofil-backend}
as=${AS:-as}
commands=${COMMANDS:-compile compile-promoted compile-allocated}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

same=0 skipped=0 status=0
for f in "$@"; do
  for c in $commands; do
    o=${c/compile/object}
    if ! "$backend" "$c" "$f" >"$work/a.s" 2>"$work/err"; then
      skipped=$((skipped + 1)); continue
    fi
    if ! "$as" -o "$work/a.o" "$work/a.s" 2>"$work/as.err"; then
      echo "skip $c $f: GNU as: $(head -1 "$work/as.err")"
      skipped=$((skipped + 1)); continue
    fi
    python3 "$here/objdump.py" "$work/a.o" >"$work/gas.txt"
    if ! "$backend" "$o" "$f" >"$work/ours.txt" 2>"$work/err"; then
      echo "NO ENCODING $c $f: $(head -1 "$work/err")"
      status=1
    elif ! cmp -s "$work/gas.txt" "$work/ours.txt"; then
      echo "DIFFER $c $f"
      diff "$work/gas.txt" "$work/ours.txt" | head -${ENCODE_DIFF_LINES:-10}
      status=1
    else
      same=$((same + 1))
    fi
  done
done
echo "encode: $same same, $skipped skipped"
exit $status
