#!/usr/bin/env bash
# The extracted Rocq model against the Prolog interpreter (docs/formal.md,
# Campaign 1): for each Fil-C IR or C file, `nanofil outcomes` prints its
# checked module and interp:run/5's outcome on each run line, and the
# model (MODEL, built from rocq/ by rocq/nix/model.nix) judges every
# line. Plain modules are skipped. Fails if any line disagrees.
#
#   MODEL=.../bin/nanofil-model agree.sh FILE...
#   NANOFIL_OPT=-O NANOFIL_CHECKS=reference agree.sh FILE...
#
# A C file is lowered by nanofil (cc-ir, needs FILCC) and its
# "// run: $fn arg..." comments become run facts, as in tests/difftest.sh.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
nanofil="$here/../bin/nanofil"
model=${MODEL:-nanofil-model}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

status=0
for f in "$@"; do
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  ir=$f
  if [[ $f == *.c ]]; then
    ir="$work/c.ir"
    (cd "$src" && "$nanofil" cc-ir "$f" </dev/null) >"$ir"
    awk '/^\/\/ run: \$/ { sub(/^\/\/ run: \$/, ""); fn = $1; $1 = ""
         sub(/^ +/, ""); gsub(/ +/, ", "); printf "run(\x27%s\x27, [%s]).\n", fn, $0 }' \
      "$f" >>"$ir"
  fi
  if ! (cd "$src" && "$nanofil" ${NANOFIL_OPT:-} outcomes "$ir" </dev/null) >"$work/out" 2>"$work/err"; then
    if grep -q 'needs a Fil-C module' "$work/err"; then continue; fi
    echo "OUTCOMES FAILED $f: $(cat "$work/err")"
    status=1
    continue
  fi
  if ! "$model" <"$work/out" >"$work/judged"; then
    echo "DISAGREE $f:"
    grep -v '^agree' "$work/judged" || true
    status=1
  else
    echo "$f $(tail -1 "$work/judged")"
  fi
done
exit $status
