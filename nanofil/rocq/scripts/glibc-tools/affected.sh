#!/usr/bin/env bash
# Compile the Rocq files you edited and every file that imports them,
# through the same per-file derivations as the push checks, and nothing
# else. With main's objects in Cachix, Nix builds only those files, and
# of the importers only those whose imports' interfaces changed: an edit
# to a glibc file's Qed proof often compiles that file alone.
#
#   nanofil/rocq/scripts/glibc-tools/affected.sh             # edits since origin/main
#   nanofil/rocq/scripts/glibc-tools/affected.sh FILE.v...   # these files
#   affected.sh --list [FILE.v...]                           # print, do not build
#
# Without FILE arguments the edits are the .v files under rocq/theories
# and rocq/glibc that differ from the merge base with origin/main, in
# commits or in the worktree. A new file must be known to git (git add
# -N) before Nix sees it. A file in runtime-concrete.txt is skipped; its
# check is nanofil-glibc-concrete.
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
list=
if [ "${1:-}" = --list ]; then list=1; shift; fi
if [ $# -eq 0 ]; then
  base=$(git merge-base HEAD origin/main)
  mapfile -t files < <({ git diff --name-only "$base"; git ls-files --others --exclude-standard; } |
    grep -E '^nanofil/rocq/(theories|glibc)/.*\.v$' | sort -u)
else
  files=("$@")
fi
model=() glibc=()
for f in "${files[@]}"; do
  n=$(basename "$f" .v)
  case $(realpath -m "$f") in
    "$repo"/nanofil/rocq/theories/*) model+=("\"$n\"") ;;
    "$repo"/nanofil/rocq/glibc/*) glibc+=("\"$n\"") ;;
    *) echo "affected.sh: $f is not under nanofil/rocq/theories or nanofil/rocq/glibc" >&2; exit 2 ;;
  esac
done
if [ ${#model[@]} -eq 0 ] && [ ${#glibc[@]} -eq 0 ]; then
  echo "affected.sh: no edited Rocq files"
  exit 0
fi
# The edited files and their importers, one installable per line.
nix eval --raw .#checks.x86_64-linux.nanofil-glibc --apply "g:
  let
      M = [ ${model[*]} ]; G = [ ${glibc[*]} ];
      any = xs: ys: builtins.any (x: builtins.elem x ys) xs;
      names = builtins.attrNames;
      models = builtins.filter (n: builtins.elem n M || any M g.model.closure.\${n}) (names g.model.vo);
      glibcs = builtins.filter (n: builtins.elem n G || any G g.closure.\${n} || any M g.modelClosure.\${n}) (names g.check);
  in builtins.concatStringsSep \"\" (
       map (n: \".#checks.x86_64-linux.nanofil-glibc.model.vo.\${n}\n\") models
       ++ map (n: \".#checks.x86_64-linux.nanofil-glibc.check.\${n}\n\") glibcs)" >"${TMPDIR:-/tmp}/affected.$$"
mapfile -t attrs <"${TMPDIR:-/tmp}/affected.$$"
rm -f "${TMPDIR:-/tmp}/affected.$$"
echo "affected.sh: ${#files[@]} edited files; they and their importers are $(grep -c 'model\.vo' <(printf '%s\n' "${attrs[@]}") || true) model and $(grep -c 'glibc.check' <(printf '%s\n' "${attrs[@]}") || true) glibc files, of which Nix compiles those whose inputs changed" >&2
if [ -n "$list" ]; then printf '%s\n' "${attrs[@]}"; exit 0; fi
exec nix build -L --no-link --keep-going "${attrs[@]}"
