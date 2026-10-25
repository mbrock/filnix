#!/usr/bin/env bash
# Audit the actual helper path, not just entry into ensure-aux. Needs gdb
# with Python, the pinned runtime's local symbols, FILCC, and nanofil's
# usual Prolog host. NANOFIL_OPT=-O audits the optimized module too.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
(
  cd "$here/../../src"
  ../bin/nanofil ${NANOFIL_OPT:-} compile \
    "$here/pointer-effects.ir" </dev/null
) >"$work/n.s"
as -o "$work/n.o" "$work/n.s"
as -o "$work/native.o" "$here/pointer-effects.s"
"${FILCC:?set FILCC to a filcc clang}" -O1 -o "$work/t" \
  "$here/pointer-effects.c" "$work/n.o" "$work/native.o"
"${GDB:-gdb}" -q -batch -x "$here/pointer-effects.gdb" "$work/t"
