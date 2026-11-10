#!/usr/bin/env bash
# The standalone compiler against the Prolog one
# (docs/gallina-backend.md, M4). For each file, what
# `nanofil-backend compile FILE.ir` prints must be, byte for byte,
# what `nanofil compile FILE.ir` prints without -O. Nothing of
# Prolog is in the backend's path: it reads the IR text itself.
# For a C or preprocessed .i file, the IR text is what
# `nanofil cc-ir` prints for it.
#
# A file is counted as
#   same     both compile it, to the same text;
#   none     nanofil compiles it and the backend does not take it
#            (exit 3): a plain module, a function outside the subset
#            or without a plan, or a form that is not ported;
#   refused  both refuse it.
# Fails if the texts differ, if the backend refuses (exit 1) what
# nanofil compiles, or if it compiles what nanofil refuses. The
# files counted as none are to be exactly those compile/none.txt
# names, so it also fails if the backend stops taking a file, or
# takes a listed one. A file's name there is its directory and
# name, as prog/setjmp.c, and for a translation unit, whose
# directory and prefix vary, its name without the prefix, as ldo.i.
#
#   BACKEND=.../nanofil-backend compile.sh FILE...
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
  echo "@@nanofil-backend $(date -u +%FT%TZ) start compile file=$f"
  ir=$f
  case $f in
    *.c | *.i)
      ir=$work/module.ir
      if ! (cd "$src" && "$nanofil" cc-ir "$f" </dev/null) >"$ir" 2>"$work/err"; then
        echo "skip $f: $(head -c 100 "$work/err" | head -1)"
        continue
      fi ;;
  esac
  case $f in
    *.i) name=$(basename "$f" | sed -E 's/^[0-9a-f]{6,8}-//') ;;
    *) name=$(basename "$(dirname "$f")")/$(basename "$f") ;;
  esac
  listed=
  if grep -qxF "$name" "$here/compile/none.txt"; then listed=1; fi
  theirs=0 ours=0
  (cd "$src" && "$nanofil" compile "$ir" </dev/null) >"$work/theirs" 2>"$work/their-err" || theirs=$?
  "$backend" compile "$ir" >"$work/ours" 2>"$work/our-err" || ours=$?
  why=$(tr -s ' \n' ' ' <"$work/our-err" | head -c 200)
  if [ "$theirs" != 0 ]; then
    if [ "$ours" = 0 ]; then
      echo "DIFFER $f: compiled, and nanofil refuses: $(head -c 200 "$work/their-err" | head -1)"
      status=1
    else
      echo "refused $f: $why"
    fi
  elif [ "$ours" = 3 ]; then
    if [ -n "$listed" ]; then
      echo "none $f: $why"
    else
      echo "DIFFER $f: not taken, and compile/none.txt does not name $name: $why"
      status=1
    fi
  elif [ "$ours" != 0 ]; then
    echo "DIFFER $f: exit $ours, and nanofil compiles: $why"
    status=1
  elif [ -n "$listed" ]; then
    echo "DIFFER $f: taken, and compile/none.txt names $name"
    status=1
  elif cmp -s "$work/ours" "$work/theirs"; then
    echo "same $f: $(wc -l <"$work/ours") lines $why"
  else
    echo "DIFFER $f: $(cmp "$work/ours" "$work/theirs" 2>&1 | head -c 200)"
    status=1
  fi
  echo "@@nanofil-backend $(date -u +%FT%TZ) done compile file=$f seconds=$((SECONDS - t0))"
done
exit $status
