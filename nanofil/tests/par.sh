#!/usr/bin/env bash
# par.sh SCRIPT FILE...: run SCRIPT FILE once per file, NANOFIL_JOBS at a
# time (default: up to four CPUs), largest files first to avoid an idle tail.
# Non-file arguments keep their order. Each run's output is printed in one block
# as soon as it finishes, followed by a line with its wall time; the exit
# status is 1 if any run failed.
set -uo pipefail
script=$1
shift
here=$(cd "$(dirname "$0")" && pwd)
jobs=${NANOFIL_JOBS:-}
if [ -z "$jobs" ]; then
  jobs=$(nproc)
  # The same 55-file group on four pinned CPUs took 57/55 s at fanout 8/4;
  # its largest compile fell from 35 to 20 s. Keep that deadline headroom.
  [ "$jobs" -le 4 ] || jobs=4
fi
echo "par: jobs=$jobs files=$# script=$script"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export PAR_WORK=$work PAR_SCRIPT=$script PAR_WATCH=$here/watch.py
python3 - "$@" <<'PY' |
import os
import sys

files = sorted(sys.argv[1:], key=lambda f: os.path.getsize(f) if os.path.isfile(f) else 0,
               reverse=True)
for i, f in enumerate(files):
    sys.stdout.buffer.write(f"{i}\0{f}\0".encode())
PY
xargs -0 -n2 -P "$jobs" bash -c '
  set -o pipefail
  out=$PAR_WORK/$0
  t0=${EPOCHREALTIME/./}
  python3 "$PAR_WATCH" --label "$(basename "$PAR_SCRIPT") $1" -- "$PAR_SCRIPT" "$1" 2>&1 \
    | tee "$out" | grep --line-buffered "^@@nanofil-" || touch "$out.failed"
  ms=$(( (${EPOCHREALTIME/./} - t0) / 1000 ))
  [ -e "$out.failed" ] && r=FAILED || r=ok
  sed "/^@@nanofil-/d" "$out"
  printf "  [%4d.%01ds] %s %s %s\n" $((ms / 1000)) $((ms % 1000 / 100)) "$(basename "$PAR_SCRIPT")" "$(basename -- "$1")" "$r"
'
# A plain glob, not compgen: Nix's non-interactive bash has no compgen.
failed=("$work"/*.failed)
if [ -e "${failed[0]}" ]; then
  echo "par: ${#failed[@]} of $# runs of $(basename "$script") failed" >&2
  exit 1
fi
