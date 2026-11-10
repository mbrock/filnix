#!/usr/bin/env bash
# The extracted emission against filc_amd64.pl's reference emission
# (docs/gallina-backend.md, M3): for each Fil-C IR or C file,
# `nanofil emit-terms` prints the ABI plan of each function and the
# asm.pl lines the reference emission gives it, as terms; the
# extracted backend (BACKEND, built by make in rocq/backend) emits
# the lines again from the plan and must get the same ones. A form
# that is not ported is a todo line: a function with one is counted
# as partial, and the lines before its first todo and after its last
# must still be the reference's. A plain module and a file nanofil
# refuses are skipped. Fails if any function differs; with
# NANOFIL_BACKEND_STRICT set, also if one is partial or refused.
#
#   BACKEND=.../nanofil-backend emit.sh FILE...
#   NANOFIL_OPT=-O emit.sh FILE...
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../../../src"
nanofil="$here/../../../bin/nanofil"
backend=${BACKEND:-$here/../nanofil-backend}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

status=0
for f in "$@"; do
  t0=$SECONDS
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  tag="opt=${NANOFIL_OPT:-plain} file=$f"
  echo "@@nanofil-backend $(date -u +%FT%TZ) start emit $tag"
  if ! (cd "$src" && "$nanofil" ${NANOFIL_OPT:-} emit-terms "$f" </dev/null) >"$work/terms" 2>"$work/err"; then
    echo "skip $f: $(head -c 100 "$work/err" | head -1)"
    continue
  fi
  if ! "$backend" emit <"$work/terms" >"$work/out" 2>"$work/err"; then
    echo "DIFFER $f: $(cat "$work/out")"
    head -c 4000 "$work/err"
    status=1
  else
    echo "same $f: $(cat "$work/out") $(tr -s ' \n' ' ' <"$work/err" | head -c 300)"
  fi
  echo "@@nanofil-backend $(date -u +%FT%TZ) done emit $tag seconds=$((SECONDS - t0))"
done
exit $status
