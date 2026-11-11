#!/usr/bin/env bash
# The spikes' C programs (docs/logic.md, docs/poison.md) are nanofil's
# actual products, as rocq/scripts/programs.sh checks for the main proofs:
# compile each with nanofil -O, print the checked module as Gallina with
# rocq/scripts/gallina.pl, and compare it with the committed *Code.v.
#
#   FILCC=.../clang rocq/spikes/code.sh            # check
#   FILCC=.../clang rocq/spikes/code.sh --update   # rewrite *Code.v
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../../src"
nanofil="$here/../../bin/nanofil"
: "${FILCC:?set FILCC to a filcc clang}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

gen_one() {
  local stem=$1 out=$2
  (cd "$src" && "$nanofil" cc-ir "$here/$stem.c" </dev/null) >"$work/$stem.ir"
  (cd "$src" && "$nanofil" -O outcomes "$work/$stem.ir" </dev/null) | grep '^module(' \
    | (cd "$here/../.." && swipl rocq/scripts/gallina.pl "$stem" "rocq/spikes/$stem.c") \
    | sed 's#rocq/scripts/programs.sh checks it is#rocq/spikes/code.sh checks it is#' >"$work/$out"
  if [ "${3:-}" = --update ]; then
    cp "$work/$out" "$here/$out"
    echo "spikes: wrote $out"
  elif diff -u "$here/$out" "$work/$out"; then
    echo "spikes: $out is rocq/spikes/$stem.c (-O)"
  else
    echo "spikes: $out differs from nanofil -O of rocq/spikes/$stem.c"
    exit 1
  fi
}

gen_one listsum ListSumCode.v "${1:-}"
gen_one sbox SboxCode.v "${1:-}"
