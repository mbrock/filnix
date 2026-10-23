#!/usr/bin/env bash
# Whole programs: each tests/c/prog/NAME.c is built by nanofil (main
# included, linked by FILCC) and by FILCC -O1 alone, and both runs must
# agree on stdout, stderr and exit status. A Fil-C safety panic counts as
# "trap" (its message names different functions in the two builds). An
# "// args: ..." line gives the arguments, and "// link: FILE.c" names a
# companion, relative to the program, that clang builds into both.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
tpl=${TPL:-tpl}
filcc=${FILCC:?set FILCC to a filcc clang}
# Corpus mode retains diagnostics and records a single outcome, rather than
# aborting the whole survey on the first unsupported program.
if [[ ${1:-} == --result ]]; then
  work=$2
  shift 2
  [[ $# == 1 ]] || { echo '--result requires exactly one source' >&2; exit 2; }
  mkdir -p "$work"
  work=$(cd "$work" && pwd)
  rm -f "$work/result"
  exec >"$work/log" 2>&1
  outcome=error
  reference_failed=0
  trap 'if [[ $reference_failed == 1 ]]; then outcome=reference-error; fi; echo "$outcome" >"$work/result"' EXIT
else
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
fi
status=0
n=0
run() {
  local exe=$1 out=$2
  shift 2
  local cwd
  cwd=$(mktemp -d "$out.cwd.XXXXXX")
  local -a run_env
  read -r -a run_env <<<"${RUN_ENV:-}"
  set +e
  # Isolate file-writing tests from the checkout and from the other run.
  # The inner shell reports a fatal signal, so keep its stderr quiet.
  (cd "$cwd" && bash -c '"$@" >"$0.stdout" 2>"$0.stderr"; exit $?' "$out" "${run_env[@]}" timeout "${PROG_TIMEOUT:-10}" "$exe" "$@" </dev/null) 2>/dev/null
  local rc=$?
  set -e
  if grep -q 'filc safety error' "$out.stderr"; then
    echo trap >"$out.stderr"
    rc='trap'
  fi
  echo "exit $rc" >"$out.status"
}
if [[ $# == 0 ]]; then set -- "$here"/c/prog/*.c; fi
for f in "$@"; do
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  name=$(basename "$f" .c)
  d="$work/$name"
  mkdir -p "$d"
  read -r -a args <<<"$(sed -n 's|^// args: ||p' "$f")"
  link=$(sed -n 's|^// link: ||p' "$f")
  libs=()
  outcome=reference-error
  reference_failed=0
  if [ -n "$link" ]; then
    "$filcc" -O1 -c -o "$d/lib.o" "$(dirname "$f")/$link"
    libs=("$d/lib.o")
  fi
  # Attempt nanofil too when the oracle fails; retain both diagnostics,
  # but never call that a measured rejection or a differential pass.
  if ! "$filcc" -O1 -w -o "$d/clang" "$f" "${libs[@]}" -lm; then reference_failed=1; fi
  outcome=reject
  if (cd "$src" && timeout "${COMPILE_TIMEOUT:-20}" "$tpl" -q main.pl -- cc "$f" </dev/null) >"$d/n.s"; then
    :
  else
    rc=$?
    if [[ $rc == 124 ]]; then outcome=compile-timeout; fi
    exit 1
  fi
  outcome=assemble-error
  as -o "$d/n.o" "$d/n.s"
  outcome='link-error'
  "$filcc" -o "$d/nanofil" "$d/n.o" "${libs[@]}" -lm
  [[ $reference_failed == 0 ]] || exit 1
  outcome=pass
  run "$d/nanofil" "$d/n" "${args[@]}"
  run "$d/clang" "$d/c" "${args[@]}"
  for part in stdout stderr status; do
    if ! diff -u "$d/c.$part" "$d/n.$part" >"$d/$part.diff"; then
      echo "MISMATCH $f ($part):"; cat "$d/$part.diff"; status=1; outcome=mismatch
    fi
  done
  # The upstream single-exec contract is combined stdout/stderr and exit 0.
  # Check the oracle as well, so undefined/nonportable tests are not passes.
  if [[ -f $f.expected ]]; then
    cat "$d/c.stdout" "$d/c.stderr" >"$d/combined"
    if ! diff -u "$f.expected" "$d/combined" || ! grep -qx 'exit 0' "$d/c.status"; then
      outcome=reference-output
      status=1
    fi
  fi
  if grep -qx 'exit 124' "$d/n.status" "$d/c.status"; then
    outcome=run-timeout
    status=1
  fi
  n=$((n + 1))
done
echo "progtest: $n programs compared"
exit $status
