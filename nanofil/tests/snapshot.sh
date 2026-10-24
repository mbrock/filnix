#!/usr/bin/env bash
# Snapshot gate: compare the working tree's compiler with REV's (default
# HEAD) on the same inputs, output for output, error messages included.
#
#   snapshot.sh [REV]
#
# Inputs are the working tree's tests (cc-ir and cc of tests/c and
# tests/filc C files, compile and print of every tests .ir) and the
# pinned cproc and c-testsuite corpora (nix/corpus.nix; set CPROC and
# CTS to their roots to skip the nix build). Needs FILCC and the
# bin/nanofil host (SWIPL, or NANOFIL_HOST=trealla with TPL). Baselines
# are cached per commit under ${SNAPSHOT_CACHE:-/tmp/nanofil-snapshot}.
# Exits 1 and lists the differing outputs if any differ.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
rev=$(git -C "$root" rev-parse "${1:-HEAD}")
cache=${SNAPSHOT_CACHE:-/tmp/nanofil-snapshot}
export FILCC=${FILCC:?set FILCC to a filcc clang}
mkdir -p "$cache"

# corpus NAME: the store path of the pinned corpus NAME.
corpus() {
  nix build --no-link --print-out-paths --impure --expr "
    let pkgs = import (builtins.getFlake \"$root\").inputs.nixpkgs { system = \"x86_64-linux\"; };
    in (import $root/nanofil/nix/corpus.nix { inherit pkgs; }).$1"
}
CPROC=${CPROC:-$(corpus cproc)}
CTS=${CTS:-$(corpus c-testsuite)}
for d in "$CPROC/test" "$CTS/tests/single-exec"; do
  [[ -d $d ]] || { echo "snapshot: no corpus at $d" >&2; exit 2; }
done

# The inputs, one "COMMAND FILE" per line, absolute paths from the
# working tree, so both compilers see the same files and messages.
inputs() {
  local t=$root/nanofil/tests f
  for f in "$t"/c/*.c "$t"/c/prog/*.c "$t"/c/reject/*.c "$t"/filc/*.c \
           "$CPROC"/test/*.c "$CTS"/tests/single-exec/*.c; do
    echo "cc-ir $f"; echo "cc $f"
  done
  find "$t" -name '*.ir' | sort | while read -r f; do
    echo "compile $f"; echo "print $f"
  done
}

# run SRC OUT: every input's output from the nanofil in SRC, into OUT.
run() {
  mkdir -p "$2"
  inputs | SRC=$1 OUT=$2 xargs -P "$(nproc)" -L1 bash -c '
    n="$0-$(tr / _ <<<"$1")"
    (cd "$SRC/nanofil/src" && timeout 300 ../bin/nanofil "$0" "$1" </dev/null) >"$OUT/$n" 2>&1
    echo "exit=$?" >>"$OUT/$n"'
}

base=$cache/$rev
if [[ ! -d $base ]]; then
  tree=$(mktemp -d)
  git -C "$root" worktree add -q --detach "$tree" "$rev"
  run "$tree" "$base.tmp"
  git -C "$root" worktree remove --force "$tree"
  mv "$base.tmp" "$base"
fi
new=$(mktemp -d)
trap 'rm -rf "$new"' EXIT
run "$root" "$new"

n=$(ls "$new" | wc -l)
if diff -rq "$base" "$new" >"$new.diff" 2>&1; then
  echo "snapshot: $n outputs identical to ${rev:0:12}"
  rm -f "$new.diff"
else
  sed "s|^Files $base/\(.*\) and .* differ\$|differs: \1|; s|$base|$rev|; s|$new|working tree|" "$new.diff"
  echo "snapshot: $(wc -l <"$new.diff") of $n outputs differ from ${rev:0:12}"
  rm -f "$new.diff"
  exit 1
fi
