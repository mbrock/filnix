#!/usr/bin/env bash
# par.sh SCRIPT FILE...: run SCRIPT FILE once per file, NANOFIL_JOBS at a
# time (default: the CPU count). Each run's output is printed in one block
# as soon as it finishes, followed by a line with its wall time; the exit
# status is 1 if any run failed.
set -uo pipefail
script=$1
shift
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export PAR_WORK=$work PAR_SCRIPT=$script
i=0
for f in "$@"; do
  printf '%s\0%s\0' "$i" "$f"
  i=$((i + 1))
done | xargs -0 -n2 -P "${NANOFIL_JOBS:-$(nproc)}" bash -c '
  out=$PAR_WORK/$0
  t0=${EPOCHREALTIME/./}
  "$PAR_SCRIPT" "$1" >"$out" 2>&1 || touch "$out.failed"
  ms=$(( (${EPOCHREALTIME/./} - t0) / 1000 ))
  [ -e "$out.failed" ] && r=FAILED || r=ok
  cat "$out"
  printf "  [%4d.%01ds] %s %s %s\n" $((ms / 1000)) $((ms % 1000 / 100)) "$(basename "$PAR_SCRIPT")" "$(basename "$1")" "$r"
'
if compgen -G "$work/*.failed" >/dev/null; then
  echo "par: $(ls "$work"/*.failed | wc -l) of $# runs of $(basename "$script") failed" >&2
  exit 1
fi
