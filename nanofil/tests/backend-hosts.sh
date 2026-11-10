#!/usr/bin/env bash
# Compare actual optimizer, pizlonator and emitter products on both
# hosts, without the C frontend or interpreter. Also exercise the CLI:
# it loads more modules and supplies the -O defaults and check passes.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=$here/../src
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
files=(interop float shadows local variadic setjmp globals copy)
inputs=()
for f in "${files[@]}"; do inputs+=("$here/filc/$f.ir"); done
for host in swi trealla; do
  (
    cd "$src"
    export NANOFIL_HOST=$host
    unset NANOFIL_STATE NANOFIL_PROFILE NANOFIL_REGISTERS NANOFIL_BRANCHES \
      NANOFIL_CHECKS NANOFIL_MEMCPY NANOFIL_INLINE NANOFIL_SIMPLIFY \
      NANOFIL_SHARE NANOFIL_BOUNDS NANOFIL_LOWERS NANOFIL_OPERANDS \
      NANOFIL_REGISTERS_LIMIT NANOFIL_SLOW_CALLS
    ../bin/nanofil --script "$here/backend-hosts.pl" "${inputs[@]}" </dev/null
    ../bin/nanofil compile "${inputs[0]}" </dev/null
    ../bin/nanofil -O compile "${inputs[0]}" </dev/null
    ../bin/nanofil -O --slow-calls=save compile "${inputs[0]}" </dev/null
  ) >"$work/$host.out" 2>"$work/$host.err"
  if [[ -s $work/$host.err ]]; then cat "$work/$host.err" >&2; exit 1; fi
  [[ -s $work/$host.out ]]
done
diff -u "$work/swi.out" "$work/trealla.out"
echo "backend hosts: ${#files[@]} fixtures + wide masks, list/stream and reference/save calls, stack/temps/pointers and CLI identical"
