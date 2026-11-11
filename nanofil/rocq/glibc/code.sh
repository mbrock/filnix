#!/usr/bin/env bash
# The glibc spike's programs (docs/glibc-ir.md) linked with nanofil's IR
# of the user glibc units they reach. For each line of the table below:
# compile the program and each glibc unit (from the capture of
# survey/glibc/capture.nix, its .filc_* module asm dropped as
# survey/glibc/run.py --drop-filc-asm does) with nanofil -O, link the
# checked modules from main with rocq/scripts/link.pl, print the result as
# Gallina with rocq/scripts/gallina.pl, and compare it with the committed
# rocq/glibc/NAMECode.v.
#
#   FILCC=.../clang rocq/glibc/code.sh [--update] [GLIBC_PP]
#
# GLIBC_PP is the capture (default: build it, about six minutes once).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nf=$(cd "$here/../.." && pwd)
src="$nf/src"
nanofil="$nf/bin/nanofil"
: "${FILCC:?set FILCC to a filcc clang}"
update=
if [ "${1:-}" = --update ]; then update=1; shift; fi
pp=${1:-$(nix build --no-link --print-out-paths -f "$nf/survey/glibc/capture.nix")}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# NAME  PROGRAM (relative to nanofil/)  GLIBC UNITS (objects of the capture)
programs='
Len rocq/glibc/len.c string/strlen.os
Say rocq/glibc/say.c string/strlen.os io/write.os
'

checked() { # checked SOURCE OUT: nanofil -O's checked module term of SOURCE
  (cd "$src" && "$nanofil" cc-ir "$1" </dev/null) >"$work/unit.ir"
  (cd "$src" && "$nanofil" -O outcomes "$work/unit.ir" </dev/null) | grep '^module(' >"$2"
}

status=0
while read -r name program units; do
  [ -n "$name" ] || continue
  lower=$(echo "$name" | tr '[:upper:]' '[:lower:]')
  checked "$nf/$program" "$work/$lower.term"
  specs=("$lower=$work/$lower.term")
  for u in $units; do
    obj=$(basename "$u" .os)
    python3 -I - "$pp/$u.i" "$work/$obj.i" <<'EOF'
import re, sys
FILC_ASM = re.compile(rb'\b(?:__asm__|__asm|asm)\s*\(\s*"\.filc_[^)]*\)\s*;')
text = open(sys.argv[1], 'rb').read()
open(sys.argv[2], 'wb').write(FILC_ASM.sub(lambda m: b"\n" * m.group(0).count(b"\n"), text))
EOF
    checked "$work/$obj.i" "$work/glibc_$obj.term"
    specs+=("glibc_$obj=$work/glibc_$obj.term")
  done
  (cd "$nf" && swipl rocq/scripts/link.pl main "${specs[@]}") >"$work/$lower.linked"
  (cd "$nf" && swipl rocq/scripts/gallina.pl "$lower" "$program with user glibc's $units, linked by rocq/scripts/link.pl" \
     rocq/glibc/code.sh <"$work/$lower.linked") >"$work/${name}Code.v"
  target="$here/${name}Code.v"
  if [ -n "$update" ]; then
    cp "$work/${name}Code.v" "$target"
    echo "glibc: wrote rocq/glibc/${name}Code.v"
  elif diff -u "$target" "$work/${name}Code.v" >"$work/diff"; then
    echo "glibc: rocq/glibc/${name}Code.v is $program with $units"
  else
    echo "glibc: rocq/glibc/${name}Code.v differs from nanofil -O of $program with $units:"
    cat "$work/diff"
    status=1
  fi
done <<<"$programs"
exit $status
