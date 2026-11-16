#!/usr/bin/env bash
# Fill a glibc proof tree with the objects that the push check's
# importers load, so that build.sh then compiles only what differs from
# them. Each file whose exported object (nix/glibc.nix: its interface, or
# the file itself) is in a binary cache, which is every file of a main
# commit that CI has checked, gets its .vo and .glob copied beside its
# source. Nothing is compiled here: a file that was
# edited, or that imports an edited file, has another derivation, which no
# cache holds, so it keeps no object and build.sh compiles it.
#
#   . env.sh; warm.sh [TREE]; build.sh TREE    # default TREE: nanofil/rocq/glibc
#
# The objects all get one modification time, later than every source, so
# make takes them as current. An edit made after warming is newer than
# its object, and make recompiles that file and its importers. The model
# objects come from env.sh (PE_MODEL), also from Nix.
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tree=$(cd "${1:-$repo/nanofil/rocq/glibc}" && pwd)
cd "$repo"
# name<TAB>output path for every general file of this checkout's sources.
nix eval --raw .#checks.x86_64-linux.nanofil-glibc --apply 'g: builtins.concatStringsSep "" (
  map (n: "${n}\t${builtins.unsafeDiscardStringContext g.exports.${n}.outPath}\n") (builtins.attrNames g.exports))' \
  >"$tree/.warm-outputs"
total=$(wc -l <"$tree/.warm-outputs")
# Substitute only: a store path argument has nothing to build, and
# --keep-going fetches every path that some cache has.
cut -f2 "$tree/.warm-outputs" | xargs nix build --no-link --keep-going 2>"$tree/.warm-log" || true
declare -A source
while read -r f; do source[$(basename "$f" .v)]=$f; done < <(find "$tree" -name '*.v')
stamp=$(mktemp)
copied=0
while IFS=$'\t' read -r name out; do
  [ -e "$out/$name.vo" ] || continue
  src=${source[$name]:-}
  [ -n "$src" ] || continue
  cp -f "$out/$name.vo" "${src%.v}.vo"
  cp -f "$out/$name.glob" "${src%.v}.glob"
  chmod u+w "${src%.v}.vo" "${src%.v}.glob"
  touch -r "$stamp" "${src%.v}.vo" "${src%.v}.glob"
  copied=$((copied + 1))
done <"$tree/.warm-outputs"
rm -f "$stamp" "$tree/.warm-outputs"
echo "warm.sh: $copied of $total files have cached objects; build.sh compiles the rest"
