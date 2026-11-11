#!/usr/bin/env bash
# The user glibc units of the Rung 2 stdlib leaves (malloc, free,
# calloc, atexit, errno, ctype, mb_cur_max, mbsinit, iswprint) as one
# linked module: each unit of the capture of survey/glibc/capture.nix,
# with its .filc_* module asm intact, compiled with nanofil -O and its
# capture command's flags (survey/glibc/run.py's cc_options), checked
# by bench/trap-checked.pl, then linked by rocq/scripts/link.pl from a
# root that names only the functions the proofs here run, so only
# what they reach is kept, printed as Gallina by rocq/scripts/gallina.pl
# and compared with the committed rocq/glibc/stdlib/StdlibCode.v.
#
#   FILCC=.../clang rocq/glibc/stdlib/code.sh [--update] [GLIBC_PP]
#
# GLIBC_PP is the capture (default: build it, about six minutes once).
# Each unit's local names become OBJECT#NAME (malloc#tcache,
# cxa_atexit#initial), the OBJECT names of the table below.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nf=$(cd "$here/../../.." && pwd)
src="$nf/src"
nanofil="$nf/bin/nanofil"
: "${FILCC:?set FILCC to a filcc clang}"
update=
if [ "${1:-}" = --update ]; then update=1; shift; fi
pp=${1:-$(nix build --no-link --print-out-paths -f "$nf/survey/glibc/capture.nix")}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
unset NANOFIL_STD NANOFIL_COMMON NANOFIL_MATH_ERRNO
if [ -z "${NANOFIL_STATE:-}" ]; then
  "$nanofil" --save-state "$work/nanofil.state" </dev/null
  export NANOFIL_STATE="$work/nanofil.state"
fi

# OBJECT  UNIT (an object of the capture)
units='
malloc malloc/malloc.os
cxa_atexit stdlib/cxa_atexit.os
atexit stdlib/atexit.oS
errno csu/errno.os
errno_loc csu/errno-loc.os
mbsinit wcsmbs/mbsinit.os
wcfuncs wctype/wcfuncs.os
ctype_info ctype/ctype-info.os
mb_cur_max locale/mb_cur_max.os
'
# The functions the proofs run, by the names callers use.
roots='malloc free calloc atexit __cxa_atexit __errno_location __ctype_b_loc
__ctype_get_mb_cur_max mbsinit iswprint'

# opts CMD: the environment and nanofil options of a capture command.
opts() {
  python3 -I - "$nf/survey/glibc/run.py" "$1" <<'EOF'
import importlib.util, shlex, sys
spec = importlib.util.spec_from_file_location("survey", sys.argv[1])
survey = importlib.util.module_from_spec(spec)
spec.loader.exec_module(survey)
env, opts = survey.cc_options(open(sys.argv[2], errors="replace").read())
print(" ".join(shlex.quote(f"{k}={v}") for k, v in sorted(env.items())))
print(" ".join(map(shlex.quote, opts)))
EOF
}

specs=()
while read -r obj unit; do
  [ -n "$obj" ] || continue
  { read -r envs; read -r flags; } < <(opts "$pp/$unit.cmd")
  eval "envs=($envs) flags=($flags)"
  (cd "$src" && env "${envs[@]}" "$nanofil" -O "${flags[@]}" cc-ir "$pp/$unit.i" </dev/null) >"$work/$obj.ir"
  (cd "$src" && env "${envs[@]}" "$nanofil" --script ../bench/trap-checked.pl "$work/$obj.ir" </dev/null) \
    >"$work/$obj.term"
  specs+=("$obj=$work/$obj.term")
done <<<"$units"

{
  printf 'module([data(stdlib_root,ro(export),8,['
  sep=
  for r in $roots; do printf "%sitem(p,sym('%s',0))" "$sep" "$r"; sep=,; done
  printf '])]).\n'
} >"$work/root.term"

(cd "$nf" && swipl rocq/scripts/link.pl stdlib_root "root=$work/root.term" "${specs[@]}") >"$work/stdlib.linked"
(cd "$nf" && swipl rocq/scripts/gallina.pl stdlib \
   "user glibc's malloc, cxa_atexit, atexit, errno, errno-loc, mbsinit, wcfuncs, ctype-info and mb_cur_max units from the roots $(echo $roots | tr ' ' ','), linked by rocq/scripts/link.pl" \
   rocq/glibc/stdlib/code.sh <"$work/stdlib.linked") >"$work/StdlibCode.v"
target="$here/StdlibCode.v"
if [ -n "$update" ]; then
  cp "$work/StdlibCode.v" "$target"
  echo "stdlib: wrote rocq/glibc/stdlib/StdlibCode.v"
elif diff -u "$target" "$work/StdlibCode.v" >"$work/diff"; then
  echo "stdlib: rocq/glibc/stdlib/StdlibCode.v is current"
else
  echo "stdlib: rocq/glibc/stdlib/StdlibCode.v differs from nanofil -O of its units:"
  cat "$work/diff"
  exit 1
fi
