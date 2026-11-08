#!/usr/bin/env bash
# The programs a Rocq proof is about (Panics.v, docs/formal.md's
# Campaign 7) are nanofil's actual products: for each line of the table
# below, compile SOURCE with nanofil (cc-ir, then `outcomes` with OPT,
# which prints the checked module), print it as Gallina with
# rocq/gallina.pl, and compare it with the committed
# rocq/theories/NAMECode.v. Fails if any differs, so a proof cannot
# silently go on describing a module nanofil no longer makes.
#
#   FILCC=.../clang rocq/programs.sh            # check
#   FILCC=.../clang rocq/programs.sh --update   # rewrite the Code.v files
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
nanofil="$here/../bin/nanofil"
: "${FILCC:?set FILCC to a filcc clang}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# NAME  SOURCE (relative to nanofil/)  OPT
programs='
Sum rocq/programs/sum.c -O
Prefix rocq/programs/prefix.c -O
Cycle rocq/programs/cycle.c -O
Hi tests/c/prog/hi.c -O
'

status=0
while read -r name source opt; do
  [ -n "$name" ] || continue
  lower=$(echo "$name" | tr '[:upper:]' '[:lower:]')
  (cd "$src" && "$nanofil" cc-ir "$here/../$source" </dev/null) >"$work/$name.ir"
  (cd "$src" && "$nanofil" $opt outcomes "$work/$name.ir" </dev/null) | grep '^module(' \
    | swipl "$here/gallina.pl" "$lower" "$source" >"$work/${name}Code.v"
  target="$here/theories/${name}Code.v"
  if [ "${1:-}" = --update ]; then
    cp "$work/${name}Code.v" "$target"
    echo "programs: wrote theories/${name}Code.v from $source ($opt)"
  elif diff -u "$target" "$work/${name}Code.v" >"$work/diff"; then
    echo "programs: theories/${name}Code.v is $source ($opt)"
  else
    echo "programs: theories/${name}Code.v differs from nanofil $opt of $source:"
    cat "$work/diff"
    status=1
  fi
done <<<"$programs"
exit $status
