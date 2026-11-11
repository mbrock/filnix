#!/usr/bin/env bash
# The native probes of the glibc spike's trusted contracts
# (docs/glibc-ir.md), every zsys-*.c here or in a subdirectory: build
# each with filcc, run it natively, and compare its standard output with
# the committed .expected file beside it.
#
#   FILCC=.../clang rocq/glibc/probe.sh
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
: "${FILCC:?set FILCC to a filcc clang}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
status=0
for c in $(find "$here" -name 'zsys-*.c' | sort); do
  name=$(basename "$c" .c)
  "$FILCC" -O1 -w "$c" -o "$work/$name"
  if "$work/$name" 2>"$work/$name.err" | diff -u "$c.expected" - ; then
    echo "probe: $name matches $name.c.expected"
  else
    echo "probe: $name differs from $name.c.expected"; cat "$work/$name.err"; status=1
  fi
done
exit $status
