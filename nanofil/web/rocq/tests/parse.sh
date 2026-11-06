#!/usr/bin/env bash
# tests/parse.sh [FILE.v...]: check rocq_syntax.pl against Rocq itself.
# Each file (default: every .v file under nanofil) is compiled as it is,
# then reprinted from its tree with every subterm in parentheses
# (reprint.pl) and compiled again in its place: if the reprint still
# type-checks and its proofs still go through, the grammar read every
# operator at Rocq's precedence and every binder where Rocq puts it. A
# sentence the grammar does not read fails too. Needs swipl and rocq (or
# coqc) with the Stdlib on ROCQPATH, as the flake's nixpkgs gives them:
#   nix shell --impure --expr 'with import (builtins.getFlake (toString ./.)).inputs.nixpkgs {}; [ swi-prolog coq coqPackages.stdlib ]'
# A file in a project (a _RocqProject or _CoqProject above it) is
# compiled with the project's -R/-Q flags, after the files listed before
# it, so a development whose files import each other is checked in order.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
if [ $# -eq 0 ]; then
  mapfile -t files < <(cd "$root" && find nanofil -name '*.v' -not -path '*/_build/*' | sort)
  set -- "${files[@]/#/$root/}"
fi
coqc=$(command -v rocq >/dev/null && echo "rocq c" || echo coqc)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
status=0

# project FILE: the directory of the project file above FILE, or FILE's own.
project() {
  local d
  d=$(cd "$(dirname "$1")" && pwd)
  while [ "$d" != / ]; do
    if [ -e "$d/_RocqProject" ] || [ -e "$d/_CoqProject" ]; then echo "$d"; return; fi
    d=$(dirname "$d")
  done
  cd "$(dirname "$1")" && pwd
}

# flags DIR: the project's -R and -Q flags.
flags() {
  local p
  for p in "$1/_RocqProject" "$1/_CoqProject"; do
    [ -e "$p" ] && grep -oE '^-[RQ] +[^ ]+ +[^ ]+' "$p" | tr '\n' ' ' && return
  done
  echo "-Q . Top"
}

# order DIR: the project's .v files in the order its project file lists them.
order() {
  local p
  for p in "$1/_RocqProject" "$1/_CoqProject"; do
    [ -e "$p" ] && grep -E '\.v$' "$p" && return
  done
  (cd "$1" && find . -name '*.v' | sed 's|^\./||' | sort)
}

for f in "$@"; do
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  proj=$(project "$f")
  rel=${f#"$proj"/}
  fl=$(flags "$proj")
  key=$(echo "$proj" | tr / _)
  orig=$tmp/orig$key
  if [ ! -d "$orig" ]; then
    cp -r "$proj" "$orig"
    while read -r v; do
      (cd "$orig" && $coqc $fl "$v" >"$tmp/log" 2>&1) || {
        echo "skip $proj/$v: it does not compile as it is" >&2
        sed 's/^/  /' "$tmp/log" >&2
      }
    done < <(order "$proj")
  fi
  rm -rf "$tmp/reprint" && cp -r "$orig" "$tmp/reprint"
  if ! swipl "$here/reprint.pl" "$f" --strict >"$tmp/reprint/$rel" </dev/null; then
    echo "FAIL $f: the grammar does not read it" >&2
    status=1
    continue
  fi
  if (cd "$tmp/reprint" && $coqc $fl "$rel" >"$tmp/log" 2>&1); then
    echo "ok   $f"
  else
    echo "FAIL $f: the reprint does not compile" >&2
    sed 's/^/  /' "$tmp/log" >&2
    status=1
  fi
done
exit $status
