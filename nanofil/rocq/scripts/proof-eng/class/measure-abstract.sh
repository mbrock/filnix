#!/usr/bin/env bash
# Measure the abstract half of the two-tree fallback after the main comparison.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
source "$root/nanofil/rocq/scripts/proof-eng/env.sh"
here="$root/nanofil/rocq/scripts/proof-eng/class"
tree="$root/.amp/in/orb-backup/class/abstract"
PE_RUNTIME=abstract "$here/../apply.sh" "$root/nanofil/rocq/glibc" "$tree"
export PE_JOBS=4
python3 "$root/nanofil/tests/watch.py" --label measure-abstract --timeout 3600 -- \
  python3 "$here/measure.py" "$tree" hello/HelloGlibcJoin.v \
  > "$tree.log" 2>&1
mkdir -p "$here/results/abstract"
cp "$tree.measure/"{times.csv,elapsed.txt,failed.txt,order.txt,machine.txt} "$here/results/abstract/"
