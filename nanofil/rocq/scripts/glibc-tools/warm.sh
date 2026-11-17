#!/usr/bin/env bash
# Fill a glibc proof tree with the objects that the push check's
# importers load, so that one.sh or build.sh then compiles only what
# differs from them. Each file whose exported object (nix/glibc.nix: its
# interface, or the file itself) is in a binary cache gets its .vo and
# .glob copied beside its source. Nothing is compiled here.
#
#   . env.sh; warm.sh [TREE]    # default TREE: nanofil/rocq/glibc
#
# CI publishes a commit's objects while its glibc push run builds them,
# so the newest commits of main may not be cached yet. When the checkout
# misses more than a tenth of its objects, warm.sh also tries the commits
# of origin/main that changed Rocq sources, newest first, and copies the
# objects of the one that has the most. It then deletes the object of
# every file whose source differs from that commit's, and of every file
# that imports a model theory that differs; make recompiles those files
# and their importers. It lists what is still missing.
#
# The objects all get one modification time, later than every source, so
# make takes them as current. An edit made after warming is newer than
# its object, and make recompiles that file and its importers. The model
# objects come from env.sh (PE_MODEL), also from Nix.
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tree=$(cd "${1:-$repo/nanofil/rocq/glibc}" && pwd)
cd "$repo"
work=$(mktemp -d)
trap 'rm -rf "$work"; git worktree remove --force "$work/old" 2>/dev/null || true' EXIT
# Nix remembers a missing path for an hour by default, but CI keeps adding
# objects; ask the cache again every time.
nixq=(--option narinfo-cache-negative-ttl 0)
# exports FLAKE: name<TAB>output path of every general file.
exports() {
  nix eval --raw "$1#checks.x86_64-linux.nanofil-glibc" --apply 'g: builtins.concatStringsSep "" (
    map (n: "${n}\t${builtins.unsafeDiscardStringContext g.exports.${n}.outPath}\n") (builtins.attrNames g.exports))' 2>/dev/null
}
# fetch LIST: substitute what the caches have; print the number present.
fetch() {
  cut -f2 "$1" | xargs nix build --no-link --keep-going "${nixq[@]}" >>"$work/log" 2>&1 || true
  n=0
  while IFS=$'\t' read -r name out; do [ -e "$out/$name.vo" ] && n=$((n + 1)); done <"$1"
  echo "$n"
}
exports . >"$work/outputs"
total=$(wc -l <"$work/outputs")
have=$(fetch "$work/outputs")
from=checkout
list=$work/outputs
if [ $((have * 10)) -lt $((total * 9)) ]; then
  echo "warm.sh: the checkout has $have of $total objects cached; trying older commits of origin/main" >&2
  best=$have
  for rev in $(git log --format=%h -n 12 origin/main -- nanofil/rocq nanofil/nix/glibc.nix nanofil/tests/rocq_interface.py); do
    git worktree remove --force "$work/old" 2>/dev/null || true
    git worktree add -q --detach "$work/old" "$rev"
    exports "$work/old" >"$work/outputs-$rev" || continue
    n=$(fetch "$work/outputs-$rev")
    echo "warm.sh: $rev has $n of $(wc -l <"$work/outputs-$rev")" >&2
    if [ "$n" -gt "$best" ]; then best=$n from=$rev list=$work/outputs-$rev; fi
    [ $((n * 10)) -ge $((total * 9)) ] && break
  done
fi
declare -A source
while read -r f; do source[$(basename "$f" .v)]=$f; done < <(find "$tree" -name '*.v')
stamp=$(mktemp -p "$work")
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
done <"$list"
stale=0
if [ "$from" != checkout ]; then
  # Objects of files that differ from that commit, or that import a model
  # theory that differs, would be wrong: delete them.
  changed=$( { git diff --name-only "$from" -- nanofil/rocq; git ls-files --others --exclude-standard nanofil/rocq; } |
    grep '\.v$' | sort -u || true)
  glibc_changed=$(printf '%s\n' $changed | { grep '^nanofil/rocq/glibc/' || true; } | xargs -r -n1 basename | sed 's/\.v$//')
  model_changed=$(printf '%s\n' $changed | { grep '^nanofil/rocq/theories/' || true; } | xargs -r -n1 basename | sed 's/\.v$//')
  drop=$(nix eval --raw .#checks.x86_64-linux.nanofil-glibc --apply "g: let
      M = [ $(printf '"%s" ' $model_changed) ];
    in builtins.concatStringsSep \"\n\" (builtins.filter (n: builtins.any (m: builtins.elem m g.modelClosure.\${n}) M) (builtins.attrNames g.exports))")
  for n in $glibc_changed $drop; do
    src=${source[$n]:-}
    if [ -n "$src" ] && [ -e "${src%.v}.vo" ]; then
      rm -f "${src%.v}.vo" "${src%.v}.glob"
      stale=$((stale + 1))
    fi
  done
fi
echo "warm.sh: copied $copied objects from $from, deleted $stale that its sources no longer match; $((total - copied + stale)) of $total files have no object"
if [ $((copied - stale)) -lt "$total" ]; then
  echo "warm.sh: build one file's imports with one.sh, or all of them with build.sh" >&2
fi
