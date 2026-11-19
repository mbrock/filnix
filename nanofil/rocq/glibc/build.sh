#!/usr/bin/env bash
# Compile the glibc spike's proofs (docs/glibc-ir.md) in _RocqProject's
# order, paths relative to this directory and subdirectories allowed,
# against compiled model theories, printing each file's time, and refuse
# Admitted or any axiom in any .v file here. Needs rocq, stdlib, std++
# and Iris on ROCQPATH. nix/glibc.nix builds the full tree in dependency order.
#
#   rocq/glibc/build.sh [THEORIES]   # default: ../theories, compiled
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
theories=${1:-$here/../theories}
cd "$here"
python3 "$here/../../tests/assumption_scan.py" .
for f in $(grep '\.v$' _RocqProject); do
  start=$(date +%s%N)
  rocq compile -R "$theories" Nanofil -R . Glibc "$f"
  ms=$((($(date +%s%N) - start) / 1000000))
  printf '@@glibc %4d.%01ds %5d lines %s\n' $((ms / 1000)) $((ms % 1000 / 100)) "$(wc -l <"$f")" "$f"
done
