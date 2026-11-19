#!/usr/bin/env bash
# Make runs this once per source. Keep the sentence log even when Rocq fails.
set -euo pipefail
source=$1
name=$(basename "$source" .v)
start=$(date +%s%N)
status=0
python3 "$tests/watch.py" --label "glibc compile $source" --warn-after 120 --timeout 900 -- \
  rocq c -q -time -R theories Nanofil -R glibc Glibc "$source" |
  tee "$out/sentence-timings/$name.log" | sed -u '/^Chars /d' || status=$?
python3 "$tests/rocq_time.py" "$source" "$out/sentence-timings/$name.log" ||
  echo "warning: Rocq sentence timing reporter failed" >&2
if ((status)); then exit "$status"; fi
ms=$((($(date +%s%N) - start) / 1000000))
printf '@@glibc %4d.%01ds %5d lines %s\n' "$((ms / 1000))" "$((ms % 1000 / 100))" \
  "$(wc -l <"$source")" "${source#glibc/}" >"times/$name"
