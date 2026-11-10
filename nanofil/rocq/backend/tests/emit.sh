#!/usr/bin/env bash
# The extracted emission against filc_amd64.pl's reference emission
# (docs/gallina-backend.md, M3). For each Fil-C IR or C file,
# `nanofil emit-terms` prints the checked module and then the asm.pl
# lines the reference emission gives it, as terms: a list for each
# item, for each weak thunk and for the end of the file. The
# extracted backend (BACKEND, built by make in rocq/backend) emits
# each list again from the module and must get the same lines.
#
# A form that is not ported is a todo line: a list with one is
# counted as partial, and the lines before its first todo and after
# its last must still be the reference's. A function the model keeps
# outside its subset is passed over, and so is one the backend builds
# no plan for, which is counted as refused.
#
# Without -O the whole module is then compared as text: what
# `nanofil-backend module` prints for the checked module must be
# what `nanofil compile` prints for the file, or `nanofil cc` for a
# preprocessed .i file, which is what nanofil-cc runs. A module with a
# function outside the subset, or with a list that is partial, has
# no whole text and is reported as `whole none`.
#
# A plain module and a file nanofil refuses are skipped. Fails if a
# list or a whole module differs; with NANOFIL_BACKEND_STRICT set,
# also if a list is partial or a function refused.
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
    whole= bad= command=compile
    case $f in *.i) command=cc ;; esac
    if [ -z "${NANOFIL_OPT:-}" ]; then
      code=0
      "$backend" module <"$work/terms" >"$work/ours" 2>"$work/whole-err" || code=$?
      if [ "$code" = 3 ]; then
        whole=", whole none"
      elif [ "$code" != 0 ]; then
        bad="no whole module: $(head -c 300 "$work/whole-err")"
      elif ! (cd "$src" && "$nanofil" "$command" "$f" </dev/null) >"$work/theirs" 2>/dev/null; then
        bad="nanofil $command failed"
      elif cmp -s "$work/ours" "$work/theirs"; then
        whole=", whole same"
      else
        bad="the whole module: $(cmp "$work/ours" "$work/theirs" 2>&1 | head -c 200)"
      fi
    fi
    if [ -n "$bad" ]; then
      echo "DIFFER $f: $bad"
      status=1
    else
      echo "same $f: $(cat "$work/out")$whole $(tr -s ' \n' ' ' <"$work/err" | head -c 300)"
    fi
  fi
  echo "@@nanofil-backend $(date -u +%FT%TZ) done emit $tag seconds=$((SECONDS - t0))"
done
exit $status
