#!/usr/bin/env bash
# The only source change in this copy is omission of the SafepointStable mode.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
source "$root/nanofil/rocq/scripts/proof-eng/env.sh"
here="$root/nanofil/rocq/scripts/proof-eng/class"
scratch="$root/.amp/in/orb-backup/class"
copy="$scratch/no-mode"
mkdir -p "$copy"
cp -a "$scratch/theories" "$scratch/glibc" "$copy/"
PE_CLASS_MODE=0 python3 "$here/convert.py" "$root/nanofil/rocq/theories" "$copy/theories"
rocq makefile -R "$copy/theories" Nanofil -R "$copy/glibc" Glibc \
  $(find "$copy/theories" "$copy/glibc" -name '*.v') -o ClassNoModeMakefile
set +e
python3 "$root/nanofil/tests/watch.py" --label class-without-mode --timeout 1800 -- \
  make -k -f ClassNoModeMakefile -j4 "$copy/glibc/libio/LibioDoAllocBase.vo" \
  "$copy/glibc/StrlenLogic.vo" > "$scratch/mode-off.log" 2>&1
status=$?
set -e
printf '%s\n' "$status" > "$here/results/mode-off-status.txt"
cp "$scratch/mode-off.log" "$here/results/"
exit "$status"
