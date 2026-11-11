#!/usr/bin/env bash
# The logic spikes' program (docs/logic.md) is nanofil's actual product,
# as rocq/scripts/programs.sh checks for the main proofs: compile listsum.c with
# nanofil -O, print the checked module as Gallina with rocq/scripts/gallina.pl,
# and compare it with the committed ListSumCode.v.
#
#   FILCC=.../clang rocq/spikes/code.sh            # check
#   FILCC=.../clang rocq/spikes/code.sh --update   # rewrite ListSumCode.v
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../../src"
nanofil="$here/../../bin/nanofil"
: "${FILCC:?set FILCC to a filcc clang}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
(cd "$src" && "$nanofil" cc-ir "$here/listsum.c" </dev/null) >"$work/listsum.ir"
(cd "$src" && "$nanofil" -O outcomes "$work/listsum.ir" </dev/null) | grep '^module(' \
  | (cd "$here/../.." && swipl rocq/scripts/gallina.pl listsum rocq/spikes/listsum.c) \
  | sed 's#rocq/scripts/programs.sh checks it is#rocq/spikes/code.sh checks it is#' >"$work/ListSumCode.v"
if [ "${1:-}" = --update ]; then
  cp "$work/ListSumCode.v" "$here/ListSumCode.v"
  echo "spikes: wrote ListSumCode.v"
elif diff -u "$here/ListSumCode.v" "$work/ListSumCode.v"; then
  echo "spikes: ListSumCode.v is rocq/spikes/listsum.c (-O)"
else
  echo "spikes: ListSumCode.v differs from nanofil -O of rocq/spikes/listsum.c"
  exit 1
fi
