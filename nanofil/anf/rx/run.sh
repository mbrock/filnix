#!/usr/bin/env bash
# The gate of the Gallina regex compiler (Rx.v): for each file of terms
# that experiments/regex-nanofil/pcre2_rx_terms.h writes, rx.pl's
# rx_file/1 under SWI-Prolog and ./rx-gallina, the extraction of Rx.v,
# must print the same bytes and must both succeed or both fail.
# rx-gallina also reads rx.pl's output with IrText.v's reader and
# requires each function there to be the term Rx.v built (`--check`).
# The gate prints each file that differs, then the number of files and
# of differences, and exits 1 when there is a difference.
#
#   nanofil/anf/rx/run.sh [FILE.pl...]
#
# The default files are tests/*.pl and, when RX_CORPUS names a
# directory, its *.pl. tests/bench.pl holds the patterns of
# experiments/regex-nanofil's bench (its dump, less two that rx.pl does
# not compile), and the other files are patterns of PCRE2 10.49's
# testinput1 and testinput2. The whole of those, 2,485 files, is what
# the hook writes as KEY.pl when PCRE2's tests run with a cache and the
# compiler ./collect, which compiles nothing:
#
#   PCRE2_RX_CACHE=DIR PCRE2_RX_COMPILER=$PWD/collect pcre2test -jit testinput1
#
# where DIR belongs to you and is writable by nobody else, and
# pcre2test is made in the hook's build of experiments/regex-nanofil's
# run.sh (`make -C $WORK/build/filc-rx pcre2test`).
# Without rocq and ocamlfind on PATH it runs itself in nix-shell
# RX_SHELL (default ../lower/shell.nix).
#   SWIPL       SWI-Prolog (default swipl on PATH)
#   RX_JOBS     files checked at once (default 4)
#   RX_TIMEOUT  seconds each program may take on a file (default 300)
#   RX_WORK     the scratch directory (default a new one under /tmp,
#               removed when there is no difference)
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
swipl=${SWIPL:-swipl}
limit=${RX_TIMEOUT:-300}

# `run.sh --one WORK FILE`: check one file, and print `OK FILE FUNCS
# UNSUPPORTED STATUS` or `DIFF FILE: WHY`.
if [[ ${1:-} == --one ]]; then
  w=$(mktemp -d "$2/one.XXXXXX")
  f=$3
  pl_status=0 v_status=0
  RX_FILE=$f timeout "$limit" "$swipl" -q \
    -g "consult('$repo/experiments/regex-nanofil/rx.pl'), getenv('RX_FILE', F), rx:rx_file(F)" \
    -t halt "$repo/nanofil/src/swi/compat.pl" </dev/null >"$w/pl.out" 2>"$w/pl.err" || pl_status=$?
  timeout "$limit" "$here/rx-gallina" --check "$w/pl.out" "$f" >"$w/v.out" 2>"$w/v.err" || v_status=$?
  why=
  if ((pl_status == 124 || v_status == 124)); then
    why="timed out (rx.pl $pl_status, rx-gallina $v_status)"
  elif ! cmp -s "$w/pl.out" "$w/v.out"; then
    why="stdout differs: $(cmp "$w/pl.out" "$w/v.out" 2>&1 | head -1 || true)"
  elif ((v_status == 3)); then
    why="term check: $(head -1 "$w/v.err" || true)"
  elif (((pl_status == 0) != (v_status == 0))); then
    why="rx.pl exits $pl_status, rx-gallina $v_status"
  fi
  if [[ -n $why ]]; then
    echo "DIFF $f: $why"
  else
    echo "OK $f $(grep -c '^func(' "$w/pl.out" || true) $(grep -c '^% ' "$w/pl.out" || true) $pl_status"
    rm -rf "$w"
  fi
  exit 0
fi

if ! command -v rocq >/dev/null || ! command -v ocamlfind >/dev/null; then
  exec nix-shell "${RX_SHELL:-$here/../lower/shell.nix}" --run "$(printf '%q ' "$0" "$@")"
fi

work=${RX_WORK:-$(mktemp -d /tmp/rx-gate.XXXXXX)}
mkdir -p "$work"
make -C "$here" >"$work/build.log" 2>&1 || { cat "$work/build.log"; exit 2; }

if (($#)); then
  files=("$@")
else
  shopt -s nullglob
  files=("$here"/tests/*.pl)
  [[ -z ${RX_CORPUS:-} ]] || files+=("$RX_CORPUS"/*.pl)
fi
jobs=${RX_JOBS:-4}
echo "$(date -u +%H:%M:%S) checking ${#files[@]} files, $jobs at a time (work: $work)"

nfiles=0 ndiff=0 nfunc=0 nunsup=0 nfail=0
while read -r tag f rest; do
  nfiles=$((nfiles + 1))
  if [[ $tag == DIFF ]]; then
    ndiff=$((ndiff + 1))
    echo "DIFF $f $rest"
  else
    read -r funcs unsup status <<<"$rest"
    nfunc=$((nfunc + funcs)) nunsup=$((nunsup + unsup))
    ((status == 0)) || nfail=$((nfail + 1))
  fi
  ((nfiles % 500)) || echo "$(date -u +%H:%M:%S) $nfiles files, $ndiff differences"
done < <(printf '%s\0' "${files[@]}" | xargs -0 -n 1 -P "$jobs" "$0" --one "$work")
# A file whose check printed no result is a difference too.
if ((nfiles != ${#files[@]})); then
  echo "DIFF: $((${#files[@]} - nfiles)) files gave no result"
  ndiff=$((ndiff + ${#files[@]} - nfiles))
  nfiles=${#files[@]}
fi
echo "files: $nfiles, differences: $ndiff" \
  "(in the files that agree, rx.pl printed $nfunc functions and $nunsup unsupported comments," \
  "and it failed on $nfail of them)"
if ((ndiff)); then
  echo "the outputs of each file that differs are in $work/one.*"
  exit 1
fi
[[ -n ${RX_WORK:-} ]] || rm -rf "$work"
