#!/usr/bin/env bash
# Snapshot gate: compare the working tree's compiler with REV's (default
# HEAD) on the same inputs, output for output, error messages included.
#
#   snapshot.sh [REV]
#
# Inputs are the working tree's tests (cc-ir and cc of tests/c and
# tests/filc C files, compile and print of every tests .ir) and the
# pinned cproc and c-testsuite corpora, and cc of each C file and
# compile of each .ir again through the middle end in three fixed modes
# ($OPT, $TMP and $INL below: the stack reference and temps, the -O
# default's registers, both without inlining, and temps with inlining).
# The corpora come from nix/corpus.nix; set CPROC and CTS to their roots
# to skip the nix build. Needs FILCC and the bin/nanofil host (SWIPL,
# or NANOFIL_HOST=trealla with TPL). Baselines are cached per commit under ${SNAPSHOT_CACHE:-/tmp/nanofil-snapshot}.
# Exits 1 and lists the differing outputs if any differ.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
rev=$(git -C "$root" rev-parse "${1:-HEAD}")
cache=${SNAPSHOT_CACHE:-/tmp/nanofil-snapshot}
export FILCC=${FILCC:?set FILCC to a filcc clang}
# Both revisions run from their sources; a saved state is one revision.
# The modes come from the command line only, the same for both.
unset NANOFIL_STATE NANOFIL_REGISTERS NANOFIL_BRANCHES NANOFIL_CHECKS NANOFIL_MEMCPY NANOFIL_INLINE NANOFIL_SIMPLIFY
# Every mode spelled out, so the -O outputs keep one mode when a
# default changes.
OPT="-O --registers=stack --branches=selected --checks=reference --memcpy=inline --inline=none --simplify=none"
TMP="-O --registers=temps --branches=selected --checks=reference --memcpy=inline --inline=none --simplify=none"
INL="-O --registers=temps --branches=selected --checks=reference --memcpy=inline --inline=small --simplify=none"
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
    echo "cc-ir $f"; echo "cc $f"; echo "$OPT cc $f"; echo "$TMP cc $f"; echo "$INL cc $f"
  done
  find "$t" -name '*.ir' | sort | while read -r f; do
    echo "compile $f"; echo "print $f"; echo "$OPT compile $f"; echo "$TMP compile $f"; echo "$INL compile $f"
  done
}

# run SRC OUT: every input's output from the nanofil in SRC, into OUT.
run() {
  mkdir -p "$2"
  # The output of "OPTIONS... COMMAND FILE" is named COMMAND-FILE, with
  # O. (stack), T. (temps) or I. (temps with inlining) before it for the
  # -O modes.
  inputs | SRC=$1 OUT=$2 xargs -P "$(nproc)" -L1 bash -c '
    set -- "$0" "$@"
    f=${!#} c=${@:$#-1:1}
    n="$c-$(tr / _ <<<"$f")"
    case "$*" in
      *inline=small*) n="I.$n" ;;
      *registers=temps*) n="T.$n" ;;
      *registers=stack*) n="O.$n" ;;
    esac
    (cd "$SRC/nanofil/src" && timeout 300 ../bin/nanofil "$@" </dev/null) >"$OUT/$n" 2>&1
    echo "exit=$?" >>"$OUT/$n"'
}

base=$cache/$rev.OTI
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
