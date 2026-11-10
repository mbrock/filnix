#!/usr/bin/env bash
# The extracted printer against asm.pl (docs/gallina-backend.md, M1):
# for each Fil-C IR or C file, `nanofil asm-terms` writes the assembly
# text and prints the asm.pl lines it is the text of, as terms; the
# extracted backend (BACKEND, built by make in rocq/backend) must
# print the same bytes from the terms. A plain module and a file
# nanofil refuses are skipped. Fails if any text differs.
#
#   BACKEND=.../nanofil-backend asm.sh FILE...
#   NANOFIL_OPT=-O asm.sh FILE...
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
  echo "@@nanofil-backend $(date -u +%FT%TZ) start asm $tag"
  if ! (cd "$src" && "$nanofil" ${NANOFIL_OPT:-} asm-terms "$f" "$work/prolog.s" </dev/null) \
      >"$work/terms" 2>"$work/err"; then
    echo "skip $f: $(head -c 100 "$work/err" | head -1)"
    continue
  fi
  if ! "$backend" <"$work/terms" >"$work/rocq.s"; then
    echo "BACKEND FAILED $f"
    status=1
  elif ! cmp "$work/prolog.s" "$work/rocq.s"; then
    echo "DIFFER $f"
    status=1
  else
    echo "same $f $(wc -l <"$work/rocq.s") lines"
  fi
  echo "@@nanofil-backend $(date -u +%FT%TZ) done asm $tag seconds=$((SECONDS - t0))"
done
exit $status
