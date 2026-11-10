#!/usr/bin/env bash
# The extracted ABI plans against filc_abi.pl (docs/gallina-backend.md,
# M2): for each Fil-C IR or C file, `nanofil abi-terms` prints the
# checked module, the plan of each of its functions and the plans of
# its weak thunks, as terms; the extracted backend (BACKEND, built by
# make in rocq/backend) builds the plans again from the module and
# must get the same terms. It reports how many plans are the same,
# how many functions the model keeps outside its subset (passed
# over), and how many of the subset the backend refuses. A plain
# module and a file nanofil refuses are skipped. Fails if any plan
# differs or any function of the subset is refused.
#
#   BACKEND=.../nanofil-backend abi.sh FILE...
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
  echo "@@nanofil-backend $(date -u +%FT%TZ) start abi file=$f"
  if ! (cd "$src" && "$nanofil" abi-terms "$f" </dev/null) >"$work/terms" 2>"$work/err"; then
    echo "skip $f: $(head -c 100 "$work/err" | head -1)"
    continue
  fi
  if ! NANOFIL_BACKEND_STRICT=1 "$backend" abi <"$work/terms" >"$work/out" 2>"$work/err"; then
    echo "DIFFER $f: $(cat "$work/out")"
    head -c 4000 "$work/err"
    status=1
  else
    echo "same $f: $(cat "$work/out")"
  fi
  echo "@@nanofil-backend $(date -u +%FT%TZ) done abi file=$f seconds=$((SECONDS - t0))"
done
exit $status
