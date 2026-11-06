#!/usr/bin/env bash
# The extracted Rocq validator against ir:valid_module/1 (docs/formal.md,
# Campaign 1): for each Fil-C IR or C file, `nanofil outcomes` prints its
# checked module, rocq/mutants.pl mutates each function, data object
# and alias (and inserts some) and has valid_module/1 judge every
# mutant, and the model (MODEL --valid) must reach the same verdict.
# Plain modules are skipped. Fails if any verdict disagrees.
#
#   MODEL=.../bin/nanofil-model valid.sh FILE...
#   NANOFIL_OPT=-O NANOFIL_CHECKS=combined valid.sh FILE...
#   NANOFIL_MUTANT_JOBS=16 valid.sh LARGE.ir  # partition items, not semantics
#   NANOFIL_MUTANTS=0 valid.sh FILE...      # unchanged base verdicts only
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
nanofil="$here/../bin/nanofil"
model=${MODEL:-nanofil-model}
jobs=${NANOFIL_MUTANT_JOBS:-1}
if [ "${NANOFIL_MUTANTS:-1}" = 0 ]; then jobs=1; fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

status=0
for f in "$@"; do
  t0=$SECONDS
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  echo "@@nanofil-rocq $(date -u +%FT%TZ) start validator opt=${NANOFIL_OPT:-plain} checks=${NANOFIL_CHECKS:-reference} file=$f"
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
  # Each partition gets the same complete module. Only the items whose
  # mutants it generates differ; inserted-item verdicts belong to partition 0.
  if ! seq 0 $((jobs - 1)) | xargs -P "$jobs" -n 1 bash -ec '
    t0=$SECONDS
    args=("$7" "$5")
    if [ "${NANOFIL_MUTANTS:-1}" = 0 ]; then args=(--base); fi
    (cd "$0" && NANOFIL_STATE= "$1" --script "$2" "${args[@]}" <"$3/out") >"$3/mutants-$7"
    "$4" --valid <"$3/mutants-$7" >"$3/judged-$7"
    echo "@@nanofil-rocq $(date -u +%FT%TZ) done validator-partition file=$6 partition=$7/$5 seconds=$((SECONDS - t0))"
  ' "$src" "$nanofil" "$here/mutants.pl" "$work" "$model" "$jobs" "$f"; then
    echo "DISAGREE $f:"
    grep -hv '^agree' "$work"/judged-* | cut -c1-400 || true
    status=1
  else
    summary=$(awk '/^% agree/ { a += $3; d += $5; o += $7; s += $9; b += $11 }
      END { printf "%% agree %d, disagree %d, outside %d, stuck_both %d, bad_line %d", a, d, o, s, b }' "$work"/judged-*)
    echo "$f $summary"
  fi
  echo "@@nanofil-rocq $(date -u +%FT%TZ) done validator opt=${NANOFIL_OPT:-plain} checks=${NANOFIL_CHECKS:-reference} file=$f seconds=$((SECONDS - t0))"
done
exit $status
