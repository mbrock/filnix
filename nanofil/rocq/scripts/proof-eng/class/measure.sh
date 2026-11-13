#!/usr/bin/env bash
# Run the three layouts serially, with the same fanout and GC parameters.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
source "$root/nanofil/rocq/scripts/proof-eng/env.sh"
scratch="$root/.amp/in/orb-backup/class"
here="$root/nanofil/rocq/scripts/proof-eng/class"
native_model=$PE_MODEL
targets=(hello/HelloGlibcJoin.v hi_atexit/HiAtexitSafe.v
  stdio/PrintfBufferXsputnHeapSwitch.v libio/LibioPutsNl.v)
for file in "$scratch/functor/string/"*.v; do targets+=("string/$(basename "$file")"); done
export PE_JOBS=${PE_JOBS:-4}
for layout in functor flat glibc; do
  export PE_MODEL=$native_model
  if [ "$layout" = glibc ]; then export PE_MODEL="$scratch/theories"; fi
  python3 "$root/nanofil/tests/watch.py" --label "measure-$layout" --timeout 5400 -- \
    python3 "$here/measure.py" "$scratch/$layout" "${targets[@]}" \
    > "$scratch/measure-$layout.log" 2>&1
  mkdir -p "$here/results/$layout"
  cp "$scratch/$layout.measure/"{times.csv,elapsed.txt,failed.txt,order.txt,machine.txt} "$here/results/$layout/"
done
