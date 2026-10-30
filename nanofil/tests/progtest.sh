#!/usr/bin/env bash
# Whole programs: each tests/c/prog/NAME.c is built by nanofil (main
# included, linked by FILCC) and by FILCC -O1 alone, and both runs must
# agree on stdout, stderr and exit status. A Fil-C safety panic counts as
# "trap" (its message names different functions in the two builds). An
# "// args: ..." line gives the arguments, and "// link: FILE.c" names a
# companion, relative to the program, that clang builds into both (with
# "// link-first", before nanofil's object in its link, so the linker
# keeps the companion's weak symbols where both define one). A
# "// nanofil-link: FILE.c" companion is built by nanofil on nanofil's
# side and by clang on clang's, for symbols two nanofil objects share. With
# a "// signatures" line, nanofil must also give each function the
# fast-entry signature clang gives it (exported pizlonatedFI<Sig>_<name>): a
# wrong one still works through the generic entries, so only this sees it.
# A "// reference-opt: -O0" line builds the reference at that level
# instead of -O1, for behaviour filcc has only without optimization.
# An "// asm-lines: REGEX" line requires nanofil's assembly lines that
# match REGEX to equal those of clang -S, as sets with blanks squeezed
# (top-level asm's .symver, function objects' entries).
# With a "// trap-reason" line, a run's safety errors are compared, each
# up to the parenthesized reason that ends its first clause ("cannot
# handle inline asm (Reason)"), or else up to the first "(" or "." ("cannot
# write 56 bytes when upper - ptr = 48"), instead of counting as "trap".
# GNU vector types are on (docs/vector-access.md); a "// no-vectors" line
# compiles with --no-vectors, which refuses them, as in reject.sh.
# A "// cflags: ..." line passes those flags to clang, and nanofil
# compiles clang's preprocessing with them, as nanofil-cc does (with
# NANOFIL_STD=c23 for -std=c23 or gnu23, gnu89 for C90 modes, and
# NANOFIL_COMMON=1 for -fcommon). NANOFIL_OPT=-O turns on nanofil's
# middle end. Each run gets PROG_TIMEOUT seconds (10); a "// timeout: N"
# line raises that to N for a program whose threads spin, which crawl
# when a loaded builder oversubscribes its cores.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
nanofil="$here/../bin/nanofil"
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
  (cd "$cwd" && bash -c '"$@" >"$0.stdout" 2>"$0.stderr"; exit $?' "$out" "${run_env[@]}" timeout "$run_timeout" "$exe" "$@" </dev/null) 2>/dev/null
  local rc=$?
  set -e
  if grep -q 'filc safety error' "$out.stderr"; then
    if [[ $trap_reason == 1 ]]; then
      sed -n -e 's/^\(filc safety error: [^(]*([^)]*)\):.*/\1/p;t' \
        -e 's/^\(filc safety error: [^(.]*[^(. ]\) *[(.].*/\1/p' "$out.stderr" >"$out.reasons"
      mv "$out.reasons" "$out.stderr"
    else
      echo trap >"$out.stderr"
    fi
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
  nlink=$(sed -n 's|^// nanofil-link: ||p' "$f")
  read -r -a cflags <<<"$(sed -n 's|^// cflags: ||p' "$f")"
  ropt=$(sed -n 's|^// reference-opt: ||p' "$f"); ropt=${ropt:--O1}
  trap_reason=0; if grep -q '^// trap-reason' "$f"; then trap_reason=1; fi
  vectors=; if grep -q '^// no-vectors' "$f"; then vectors=--no-vectors; fi
  run_timeout=${PROG_TIMEOUT:-10}
  tmo=$(sed -n 's|^// timeout: ||p' "$f")
  if [[ -n $tmo ]] && (( tmo > run_timeout )); then run_timeout=$tmo; fi
  input=$f std=c17 common=
  if [[ " ${cflags[*]} " =~ \ -fcommon\  ]]; then common=1; fi
  if [[ " ${cflags[*]} " =~ \ -std=(c|gnu)(23|2x)\  ]]; then std=c23; fi
  if [[ " ${cflags[*]} " =~ \ (-std=(c|gnu)(89|90)|-ansi|-fgnu89-inline)\  ]]; then std=gnu89; fi
  libs=()
  outcome=reference-error
  reference_failed=0
  if [ -n "$link" ]; then
    "$filcc" -O1 -c -o "$d/lib.o" "$(dirname "$f")/$link"
    libs=("$d/lib.o")
  fi
  # Attempt nanofil too when the oracle fails; retain both diagnostics,
  # but never call that a measured rejection or a differential pass.
  if [ ${#cflags[@]} != 0 ]; then
    input=$d/$name.i
    "$filcc" "${cflags[@]}" -E -o "$input" "$f"
  fi
  clibs=() nlibs=()
  if [ -n "$nlink" ]; then
    "$filcc" -O1 -w -c -o "$d/nlib-clang.o" "$(dirname "$f")/$nlink"
    (cd "$src" && NANOFIL_COMMON=$common timeout "${COMPILE_TIMEOUT:-20}" "$nanofil" ${NANOFIL_OPT:-} cc "$(dirname "$f")/$nlink" </dev/null) >"$d/nlib.s"
    as -o "$d/nlib.o" "$d/nlib.s"
    clibs=("$d/nlib-clang.o") nlibs=("$d/nlib.o")
  fi
  if ! "$filcc" "${cflags[@]}" "$ropt" -w -o "$d/clang" "$f" "${libs[@]}" "${clibs[@]}" -lm; then reference_failed=1; fi
  outcome=reject
  if (cd "$src" && NANOFIL_STD=$std NANOFIL_COMMON=$common timeout "${COMPILE_TIMEOUT:-20}" "$nanofil" ${NANOFIL_OPT:-} ${vectors} cc "$input" </dev/null) >"$d/n.s"; then
    :
  else
    rc=$?
    if [[ $rc == 124 ]]; then outcome=compile-timeout; fi
    exit 1
  fi
  outcome=assemble-error
  as -o "$d/n.o" "$d/n.s"
  outcome='link-error'
  if grep -q '^// link-first' "$f"; then
    "$filcc" -o "$d/nanofil" "${libs[@]}" "$d/n.o" "${nlibs[@]}" -lm
  else
    "$filcc" -o "$d/nanofil" "$d/n.o" "${nlibs[@]}" "${libs[@]}" -lm
  fi
  [[ $reference_failed == 0 ]] || exit 1
  outcome=pass
  if grep -q '^// signatures' "$f"; then
    "$filcc" "${cflags[@]}" -O1 -w -S -o "$d/c.s" "$f"
    for s in n c; do
      grep -oE 'globl[[:space:]]+pizlonatedFI[0-9]+_[A-Za-z0-9_]+' "$d/$s.s" | awk '{print $2}' | sort >"$d/$s.sigs" || true
    done
    if ! diff -u "$d/c.sigs" "$d/n.sigs" >"$d/sigs.diff"; then
      echo "MISMATCH $f (signatures):"; cat "$d/sigs.diff"; status=1; outcome=mismatch
    fi
  fi
  asm_lines=$(sed -n 's|^// asm-lines: ||p' "$f")
  if [ -n "$asm_lines" ]; then
    "$filcc" "${cflags[@]}" -O1 -w -S -o "$d/c.s" "$f"
    for s in n c; do grep -E "$asm_lines" "$d/$s.s" | sed 's/^[[:space:]]*//; s/[[:space:]]\{1,\}/ /g' | sort >"$d/$s.lines" || true; done
    if ! diff -u "$d/c.lines" "$d/n.lines" >"$d/lines.diff"; then
      echo "MISMATCH $f (asm lines):"; cat "$d/lines.diff"; status=1; outcome=mismatch
    fi
  fi
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
