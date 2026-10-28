#!/usr/bin/env bash
# Retired register modes are refused, by option and by NANOFIL_REGISTERS:
# no output, a nonzero exit and a message naming the modes that remain
# (docs/perf.md, register modes). Needs the bin/nanofil host.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nanofil="$here/../bin/nanofil"
input="$here/fixtures/copy.ir"
status=0
refused() { # LABEL WANT [ENV...] -- ARGS...
  local label=$1 want=$2 out err rc
  shift 2
  err=$(mktemp)
  out=$(cd "$here/../src" && env "$@" compile "$input" </dev/null 2>"$err")
  rc=$?
  if [ $rc -eq 0 ] || [ -n "$out" ] || ! grep -qF "$want" "$err"; then
    echo "registers.sh: $label: exit $rc, $(wc -c <<<"$out") bytes of output, stderr: $(cat "$err")" >&2
    status=1
  fi
  rm -f "$err"
}
for mode in local function operands cells flow; do
  want="registers=$mode was retired (docs/perf.md); registers must be stack or temps"
  refused "--registers=$mode" "$want" "$nanofil" -O "--registers=$mode"
  refused "NANOFIL_REGISTERS=$mode" "$want" NANOFIL_REGISTERS=$mode "$nanofil" -O
done
refused "--registers=bogus" "registers must be stack or temps" "$nanofil" --registers=bogus
for mode in stack temps; do
  if ! (cd "$here/../src" && "$nanofil" -O "--registers=$mode" compile "$input" </dev/null >/dev/null); then
    echo "registers.sh: --registers=$mode failed" >&2
    status=1
  fi
done
[ $status -eq 0 ] && echo "registers.sh: retired modes refused, stack and temps accepted"
exit $status
