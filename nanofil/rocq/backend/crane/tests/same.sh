#!/usr/bin/env bash
# The C++ extraction against the OCaml one (docs/gallina-backend.md,
# M6), for a command Prolog has no counterpart of. For each IR file,
# `nanofil-backend-cpp COMMAND FILE.ir` must exit as
# `nanofil-backend COMMAND FILE.ir` does, print the same bytes, and
# say the same on stderr. COMMAND is compile-allocated unless set
# (M7, Regs.v): what that prints is held to the programs' behavior by
# tests/regs.sh on the OCaml build, and here to the same text.
#
# A file is counted as
#   same     both compile it, to the same text;
#   none     neither takes it (exit 3), for the same reason;
#   refused  both refuse it (exit 1), for the same reason.
# Fails on any difference, and on any other exit status.
#
#   BACKEND=.../nanofil-backend-cpp REFERENCE=.../nanofil-backend same.sh FILE.ir...
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
backend=${BACKEND:-$here/../nanofil-backend-cpp}
reference=${REFERENCE:-$here/../../nanofil-backend}
command=${COMMAND:-compile-allocated}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

status=0
for f in "$@"; do
  t0=$SECONDS
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  echo "@@nanofil-backend-crane $(date -u +%FT%TZ) start $command file=$f"
  theirs=0 ours=0
  "$reference" "$command" "$f" >"$work/theirs" 2>"$work/their-err" || theirs=$?
  "$backend" "$command" "$f" >"$work/ours" 2>"$work/our-err" || ours=$?
  why=$(tr -s ' \n' ' ' <"$work/our-err" | head -c 200)
  if [ "$ours" != "$theirs" ]; then
    echo "DIFFER $f: exit $ours, and the OCaml build's is $theirs: $why"
    status=1
  elif ! cmp -s "$work/ours" "$work/theirs"; then
    echo "DIFFER $f: $(cmp "$work/ours" "$work/theirs" 2>&1 | head -c 200)"
    status=1
  elif ! cmp -s "$work/our-err" "$work/their-err"; then
    echo "DIFFER $f: says $why, and the OCaml build $(tr -s ' \n' ' ' <"$work/their-err" | head -c 200)"
    status=1
  else
    case $ours in
      0) echo "same $f: $(wc -l <"$work/ours") lines" ;;
      1) echo "refused $f: $why" ;;
      3) echo "none $f: $why" ;;
      *) echo "DIFFER $f: both exit $ours: $why"; status=1 ;;
    esac
  fi
  echo "@@nanofil-backend-crane $(date -u +%FT%TZ) done $command file=$f seconds=$((SECONDS - t0))"
done
exit $status
