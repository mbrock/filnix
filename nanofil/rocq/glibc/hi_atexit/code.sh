#!/usr/bin/env bash
# The fixture of rocq/glibc/hi_atexit.c (docs/glibc-ir.md) linked with
# the 32 user glibc units it reaches: `atexit(close_stdout_hi);
# puts("hello"); exit(0);`, where close_stdout_hi asks `__fpending` and
# `ferror` of stdout, closes it and calls `_exit(1)` on an error.
#
# The program is compiled with nanofil -O checked-terms, and each glibc
# unit (from the capture of survey/glibc/capture.nix) as nanofil-cc
# would, with the environment and options survey/glibc/run.py's
# cc_options reads from its compile command, as rocq/glibc/libio/code.sh
# does. rocq/scripts/link.pl --ctors links them from `main`, keeping
# stdfiles' constructor `_IO_stdfiles_init`. Each unit is linked under
# the object name the narrower fixtures give it (stdlib/code.sh's
# `malloc`, `cxa_atexit`, `atexit`, `errno`, `errno_loc`, libio/code.sh's
# and string/code.sh's `glibc_<unit>`), so every local name, and so
# every function, is the same term in this module as in StdlibCode.v,
# LenCode.v, MemFwdCode.v and the Libio*Code.v fixtures.
#
# The linked module is long, so rocq/scripts/gallina.pl --chunk prints
# it once and slice.py cuts the print into files HiAtexitCode01.v to
# HiAtexitCodeNN.v of at most about 550 lines, each a list of whole items
# (hi_items_K) or of the blocks of one function too long for a file
# (hi_blocks_K), and HiAtexitTerm.v joins the item lists into
# hi_atexit_term. Each file is compared with the committed one, or
# rewritten with --update.
#
#   FILCC=.../clang rocq/glibc/hi_atexit/code.sh [--update] [GLIBC_PP]
#
# GLIBC_PP is the capture (default /tmp/glibc-pp if it exists, else
# build it, about six minutes once). Needs swipl on PATH.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nf=$(cd "$here/../../.." && pwd)
nanofil="$nf/bin/nanofil"
: "${FILCC:?set FILCC to a filcc clang, whose macros hi_atexit.c is read with}"
update=
if [ "${1:-}" = --update ]; then update=1; shift; fi
if [ -n "${1:-}" ]; then pp=$1
elif [ -d /tmp/glibc-pp ]; then pp=/tmp/glibc-pp
else pp=$(nix build --no-link --print-out-paths -f "$nf/survey/glibc/capture.nix"); fi
work=$(mktemp -d)
trap '[ -n "${KEEP:-}" ] || rm -rf "$work"' EXIT
(cd "$nf/src" && "$nanofil" --save-state "$work/nanofil.state" </dev/null)
export NANOFIL_STATE="$work/nanofil.state"
unset NANOFIL_STD NANOFIL_COMMON NANOFIL_MATH_ERRNO

# OBJECT UNIT (an object of the capture). The last names are those of
# libio/code.sh and string/code.sh: glibc_ and the unit's base name.
units='
malloc malloc/malloc.os
cxa_atexit stdlib/cxa_atexit.os
atexit stdlib/atexit.oS
errno csu/errno.os
errno_loc csu/errno-loc.os
- libio/__fpending.os libio/ferror.os libio/filedoalloc.os libio/fileops.os libio/genops.os
- libio/iofclose.os libio/iofputs.os libio/ioputs.os libio/stdfiles.os libio/stdio.os libio/vtables.os
- termios/isatty_nostatus.os io/write.os io/write_nocancel.os io/lseek64.os io/fstat64.os
- io/close_nocancel.os io/close_nocancel_nostatus.os posix/_exit.os stdlib/exit.os
- stdlib/cxa_thread_atexit_impl.os nptl/libc-cleanup.os misc/single_threaded.os misc/makedev.os
- string/strlen.os string/mempcpy.os string/memcpy.os
'

checked() { # checked UNIT OUT: the checked module nanofil-cc compiles UNIT to
  local envs opts
  read -r envs opts < <(python3 - "$pp/$1.cmd" "$nf/survey/glibc/run.py" <<'EOF'
import importlib.util, sys
spec = importlib.util.spec_from_file_location("run", sys.argv[2])
run = importlib.util.module_from_spec(spec); spec.loader.exec_module(run)
env, opts = run.cc_options(open(sys.argv[1]).read())
print(",".join(f"{k}={v}" for k, v in env.items()) or "-", " ".join(opts))
EOF
)
  [ "$envs" = - ] && envs=
  (cd "$nf/src" && env ${envs//,/ } "$nanofil" -O $opts checked-terms "$pp/$1.i" </dev/null) >"$2"
}

(cd "$nf/src" && "$nanofil" -O checked-terms "$nf/rocq/glibc/hi_atexit.c" </dev/null) >"$work/hi_atexit.term"
specs=("hi_atexit=$work/hi_atexit.term")
while read -r obj rest; do
  [ -n "$obj" ] || continue
  if [ "$obj" = - ]; then
    for u in $rest; do
      o=glibc_$(basename "$u" | sed 's/\.o[sS]$//' | tr - _)
      checked "$u" "$work/$o.term"
      specs+=("$o=$work/$o.term")
    done
  else
    checked "$rest" "$work/$obj.term"
    specs+=("$obj=$work/$obj.term")
  fi
done <<<"$units"
[ "${#specs[@]}" = 33 ] || { echo "hi_atexit: expected the program and 32 units, got ${#specs[@]}" >&2; exit 1; }
(cd "$nf" && swipl rocq/scripts/link.pl --ctors main "${specs[@]}") >"$work/hi.linked"

# The whole module printed once, then cut into slices of whole items
# by rocq/glibc/hi_atexit/slice.py, a function longer than a slice into
# lists of its blocks.
(cd "$nf" && swipl rocq/scripts/gallina.pl --chunk hi_atexit \
   "rocq/glibc/hi_atexit.c linked with its 32 user glibc units by rocq/scripts/link.pl --ctors" \
   rocq/glibc/hi_atexit/code.sh <"$work/hi.linked") >"$work/hi.v"
mkdir -p "$work/out"
n=$(python3 -I "$here/slice.py" "$work/hi.v" "$work/out")

status=0
emit() { # emit FILE: compare FILE with the committed one, or write it
  local f=$1 target="$here/$(basename "$1")"
  if [ -n "$update" ]; then
    cp "$f" "$target"
    echo "glibc: wrote rocq/glibc/hi_atexit/$(basename "$f")"
  elif diff -u "$target" "$f" >"$work/diff"; then
    echo "glibc: rocq/glibc/hi_atexit/$(basename "$f") is current"
  else
    echo "glibc: rocq/glibc/hi_atexit/$(basename "$f") differs from nanofil -O of hi_atexit.c and its units:"
    cat "$work/diff"
    status=1
  fi
}
for k in $(seq -w 1 "$n" | sed "s/^[0-9]$/0&/"); do emit "$work/out/HiAtexitCode$k.v"; done

emit "$work/out/HiAtexitTerm.v"
for f in "$here"/HiAtexitCode[0-9]*.v; do
  [ -e "$f" ] || continue
  k=$(basename "$f" .v | sed 's/HiAtexitCode0*//')
  [ "$k" -le "$n" ] || { echo "glibc: rocq/glibc/hi_atexit/$(basename "$f") is past the $n slices"; status=1; }
done
exit $status
