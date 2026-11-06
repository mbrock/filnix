#!/usr/bin/env bash
# The extracted Rocq validator against ir:valid_module/1 (docs/formal.md,
# Campaign 1): for each Fil-C IR or C file, `nanofil outcomes` prints its
# checked module, rocq/mutants.pl mutates each function and has
# valid_module/1 judge every mutant, and the model (MODEL --valid) must
# reach the same verdict. Plain modules are skipped. Fails if any
# verdict disagrees.
#
#   MODEL=.../bin/nanofil-model valid.sh FILE...
#   NANOFIL_OPT=-O NANOFIL_CHECKS=combined valid.sh FILE...
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
  fi
  if ! (cd "$src" && "$nanofil" ${NANOFIL_OPT:-} outcomes "$ir" </dev/null) >"$work/out" 2>"$work/err"; then
    if grep -q 'needs a Fil-C module' "$work/err"; then continue; fi
    echo "OUTCOMES FAILED $f: $(cat "$work/err")"
    status=1
    continue
  fi
  (cd "$src" && NANOFIL_STATE= "$nanofil" --script "$here/mutants.pl" <"$work/out") >"$work/mutants"
  if ! "$model" --valid <"$work/mutants" >"$work/judged"; then
    echo "DISAGREE $f:"
    grep -v '^agree' "$work/judged" | cut -c1-400 || true
    status=1
  else
    echo "$f $(tail -1 "$work/judged")"
  fi
done
exit $status
