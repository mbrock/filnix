#!/usr/bin/env bash
# One arithmetic, three readings (docs/arith.md): every generated C
# integer constant expression is read by c_types' const_eval, by the
# interpreter on c_lower's IR, and by clang (FILCC, default clang).
# Fails when the readings disagree where they must agree.
#
#   arith.sh slice                      the Nix check's regression slice
#   arith.sh complete                   every operator over boundary leaves
#   arith.sh random SEED COUNT DEPTH    seeded random trees up to DEPTH
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cd "$here/../src"
"$here/../bin/nanofil" --script ../tests/arith.pl "$work" "$@" </dev/null
