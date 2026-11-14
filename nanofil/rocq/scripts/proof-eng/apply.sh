#!/usr/bin/env bash
# Rewrite a copy of the glibc proof tree with the stages in stages/ that
# main does not have yet, in name order, and then lay the files of overlay/
# over the result.
#
#   apply.sh SRC DST    # SRC is rocq/glibc of main; DST is replaced
#
# Each stage is a program called with the tree as its only argument. It
# rewrites the tree in place and must give the same output for the same
# input. overlay/ holds files written by hand: new files, and whole
# replacements of files that no stage can produce.
#
# stages/landed.txt names the stages whose output is on main. They are
# skipped, because a stage does not accept its own output as input.
# PE_STAGES=all runs every stage: use it on a tree in the layout that
# main had before the first cutover, such as an old checkout that holds
# a proof file which was never merged. PE_STAGES can also name the
# stages to run, as in PE_STAGES="50-program.py 60-memory-rules.py" for
# a flat tree from between the two cutovers.
#
# With PE_RUNTIME=abstract a flat copy declares the runtime of Fix.v as
# an abstract Runtime before any stage runs, as abstract-general.sh does.
# Stage 10 makes that choice when it writes Fix.v for an old-layout tree.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=$1
dst=$2
rm -rf "$dst"
mkdir -p "$(dirname "$dst")"
cp -r "$src" "$dst"
find "$dst" \( -name '*.vo*' -o -name '*.glob' -o -name '.*.aux' \) -delete
if [ "${PE_RUNTIME:-interp}" = abstract ] && [ -f "$dst/Fix.v" ]; then
  binding='Module R := InterpRuntime.'
  if [ "$(grep -cxF "$binding" "$dst/Fix.v")" != 1 ]; then
    echo "apply: Fix.v must bind the interpreter runtime exactly once" >&2
    exit 2
  fi
  sed -i "s/^$binding\$/Declare Module R : Runtime./" "$dst/Fix.v"
fi
landed=$(sed 's/#.*//; s/[[:space:]]*$//; /^$/d' "$here/stages/landed.txt")
for name in ${PE_STAGES:-}; do
  if [ "$name" != all ] && [ ! -f "$here/stages/$name" ]; then
    echo "apply: PE_STAGES names no stage: $name" >&2
    exit 2
  fi
done
for stage in "$here"/stages/*.py; do
  case " ${PE_STAGES:-} " in
    "  ") if grep -qxF "$(basename "$stage")" <<<"$landed"; then continue; fi ;;
    " all ") ;;
    *" $(basename "$stage") "*) ;;
    *) continue ;;
  esac
  echo "@@proof-eng stage $(basename "$stage")" >&2
  python3 -I "$stage" "$dst"
done
if [ -d "$here/overlay" ]; then
  cp -r "$here/overlay/." "$dst/"
fi
python3 -I "$here/stages/10-flatten.py" "$dst" --check-names-only
