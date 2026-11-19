#!/usr/bin/env bash
# Check that the constant-time comparison proof still describes the
# checked IR nanofil generates for its C fixture.
#
#   FILCC=.../clang rocq/scripts/programs.sh            # check
#   FILCC=.../clang rocq/scripts/programs.sh --update   # rewrite CtLtCode.v
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../../src"
nanofil="$here/../../bin/nanofil"
: "${FILCC:?set FILCC to a filcc clang}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

source=rocq/theories/logic/ct_lt.c
target="$here/../theories/logic/CtLtCode.v"
(cd "$src" && "$nanofil" cc-ir "$here/../../$source" </dev/null) >"$work/ct_lt.ir"
(cd "$src" && "$nanofil" -O outcomes "$work/ct_lt.ir" </dev/null) | grep '^module(' \
  | swipl "$here/gallina.pl" ctlt "$source" >"$work/CtLtCode.v"
if [ "${1:-}" = --update ]; then
  cp "$work/CtLtCode.v" "$target"
else
  diff -u "$target" "$work/CtLtCode.v"
  echo "CtLtCode.v matches nanofil -O of $source"
fi
