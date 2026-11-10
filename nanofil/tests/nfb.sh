#!/usr/bin/env bash
# The NFB round trip (docs/nfb.md): for each IR or C file, `nanofil
# nfb-check` writes the module, and a Fil-C module's checked module, as
# NFB and reads each back. With NAMES and CONTEXT the reading is the very
# module; without them it is a module whose encoding is the same core
# words. A file nanofil refuses for another reason is skipped; a failure
# of the encoder or the reader fails the run.
#
#   nfb.sh FILE...                  (FILCC for C files)
#   NANOFIL_OPT=-O nfb.sh FILE...   after the middle end
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
nanofil="$here/../bin/nanofil"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

status=0
for f in "$@"; do
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  # shellcheck disable=SC2086
  if (cd "$src" && "$nanofil" ${NANOFIL_OPT:-} nfb-check "$f" </dev/null) >"$work/out" 2>"$work/err"; then
    cat "$work/out"
  elif grep -q 'nfb\|read back' "$work/err"; then
    echo "FAIL $f"
    cat "$work/out" "$work/err"
    status=1
  else
    echo "skip $f: $(head -1 "$work/err" | head -c 120)"
  fi
done
exit $status
