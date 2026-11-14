#!/usr/bin/env bash
# Make a git worktree of HEAD whose rocq/glibc is the pipeline's output,
# staged, so that Nix builds the gates on it:
#
#   materialize.sh DIR
#   nix build -L DIR#checks.x86_64-linux.nanofil-glibc
#
# The stages and the overlay come from this checkout, uncommitted edits
# included. Everything else comes from the HEAD commit, so commit a change
# outside rocq/glibc before testing it here. DIR is scratch: an existing
# worktree there is reset to HEAD.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
dir=$1
head=$(git -C "$repo" rev-parse HEAD)
if [ -e "$dir/.git" ]; then
  git -C "$dir" reset -q --hard "$head"
  git -C "$dir" clean -q -fd nanofil/rocq/glibc
else
  git -C "$repo" worktree add -q --detach "$dir" "$head"
fi
tmp=$(mktemp -d)
"$here/apply.sh" "$dir/nanofil/rocq/glibc" "$tmp/glibc"
rm -rf "$dir/nanofil/rocq/glibc"
mv "$tmp/glibc" "$dir/nanofil/rocq/glibc"
# Stage 50 retains compiler metadata and its input beside the output tree.
# Materialization only needs the output; regeneration retains review evidence.
rm -rf "$tmp"
git -C "$dir" add -A nanofil/rocq/glibc
git -C "$dir" status --short | awk '{ n[substr($0, 1, 1)]++ } END { for (k in n) printf "%s %d\n", k, n[k] }'
