#!/usr/bin/env bash
# This script reproduces the option parser from captured user glibc sources.
# It compiles both translation units with their recorded options and links
# them once, so private symbols keep the same names in every proof fixture.
# The slicer preserves complete blocks while keeping each file small.
#
# Usage: code.sh [--update] GLIBC_PP
# GLIBC_PP is the output of survey/glibc/capture.nix at this repository pin.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nf=$(cd "$here/../../.." && pwd)
update=
if [ "${1:-}" = --update ]; then update=1; shift; fi
pp=${1:?pass the pinned glibc capture directory}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
(cd "$nf/src" && ../bin/nanofil --save-state "$work/nanofil.state" </dev/null)
export NANOFIL_STATE="$work/nanofil.state"
unset NANOFIL_STD NANOFIL_COMMON NANOFIL_MATH_ERRNO
for unit in getopt getopt1; do
  mapfile -t options < <(python3 - "$nf/survey/glibc/run.py" "$pp/posix/$unit.os.cmd" <<'PY'
import importlib.util, shlex, sys
spec = importlib.util.spec_from_file_location("survey", sys.argv[1])
survey = importlib.util.module_from_spec(spec)
spec.loader.exec_module(survey)
env, options = survey.cc_options(open(sys.argv[2]).read())
print(" ".join(shlex.quote(f"{k}={v}") for k, v in sorted(env.items())))
print(" ".join(map(shlex.quote, options)))
PY
)
  eval "envs=(${options[0]}) flags=(${options[1]})"
  (cd "$nf/src" && env "${envs[@]}" ../bin/nanofil -O "${flags[@]}" \
    checked-terms "$pp/posix/$unit.os.i" </dev/null) >"$work/$unit.term"
done
(cd "$nf" && swipl rocq/scripts/link.pl getopt_long \
  "glibc_getopt=$work/getopt.term" "glibc_getopt1=$work/getopt1.term") >"$work/linked.term"
(cd "$nf" && swipl rocq/scripts/gallina.pl --chunk getopt \
  "user glibc's getopt and getopt1 units linked from getopt_long" \
  rocq/glibc/getopt/code.sh <"$work/linked.term") >"$work/Getopt.v"
python3 "$here/slice.py" "$work/Getopt.v" "$work"
status=0
for out in "$work"/GetoptCode[0-9]*.v "$work/GetoptTerm.v"; do
  target="$here/$(basename "$out")"
  if [ -n "$update" ]; then cp "$out" "$target"
  elif ! diff -u "$target" "$out"; then status=1; fi
done
for target in "$here"/GetoptCode[0-9]*.v; do
  if [ ! -f "$work/$(basename "$target")" ]; then
    echo "stale fixture: $target" >&2
    status=1
  fi
done
[ "$status" != 0 ] || echo "getopt: all generated fixtures are current"
exit "$status"
