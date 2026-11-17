#!/usr/bin/env bash
# Add the inferred Proof using clauses (proof-using.py) to the section
# proofs of the glibc files under the given directories of the checkout,
# and check that no declaration's type changed.
#
#   . env.sh; proof-using.sh TREE DIR...    # DIR relative to rocq/glibc, such as libio
#
# TREE is a compiled copy of the checkout's rocq/glibc (warm.sh, then
# build.sh). For each file under DIR with a kept section proof, Rocq
# prints its suggestions while compiling it in TREE, and proof-using.py
# rewrites the checkout's file. TREE then gets the new files, and make
# recompiles them, not their importers. "Print Module" of every rewritten file, before and
# after, must agree, which shows that every lemma kept its type. The
# report is in TREE.proof-using/.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
glibc=$repo/nanofil/rocq/glibc
tree=$(cd "$1" && pwd)
shift
out=$tree.proof-using
rm -rf "$out"
mkdir -p "$out/logs" "$out/before" "$out/after" "$out/scratch"
files=$(cd "$glibc" && for d in "$@"; do find "$d" -name '*.v'; done | sort)
# The files whose interface keeps a proof.
todo=$(cd "$glibc" && python3 "$repo/nanofil/tests/rocq_interface.py" --stats $files |
  awk '$5 != "total" && $3 > 0 { print $5 }')
logical() { local f=${1%.v}; echo "Glibc.${f//\//.}"; }
query() { # query FILE DIR: Print Module of FILE's library, against TREE.
  local d
  d=$(mktemp -d)
  printf 'Require %s.\nPrint Module %s.\n' "$(logical "$1")" "$(logical "$1")" >"$d/Q.v"
  (cd "$tree" && rocq c -q -R "$PE_MODEL" Nanofil -R . Glibc "$d/Q.v") >"$2/$(echo "$1" | tr / _).txt" 2>&1
  rm -rf "$d"
}
export -f query logical
export tree PE_MODEL
printf '%s\n' $todo | xargs -P 16 -I{} bash -c 'query {} '"$out/before"
printf '%s\n' $todo | xargs -P 16 -I{} bash -c '
  f={}; o='"$out"'/scratch/${f%.v}.vo; mkdir -p "$(dirname "$o")"
  cd "$tree" && rocq c -q -set "Suggest Proof Using" -R "$PE_MODEL" Nanofil -R . Glibc -o "$o" "$f" \
    >'"$out"'/logs/$(echo "$f" | tr / _).log 2>&1 || echo "FAIL suggestions $f"'
status=0
for f in $todo; do
  python3 "$here/proof-using.py" "$glibc/$f" "$out/logs/$(echo "$f" | tr / _).log" >>"$out/rewritten" || status=1
  cp "$glibc/$f" "$tree/$f"
done
# Recompile only the rewritten files, in import order. Their types do not
# depend on their importers, which the Nix gate compiles.
(cd "$tree" && rocq dep -R "$PE_MODEL" Nanofil -R . Glibc $(find . -name '*.v' | sed 's|^\./||' | sort)) \
  >"$out/deps" 2>"$out/dep.err"
cat >"$out/Makefile" <<MK
%.vo: %.v
	@rocq c -q -R $PE_MODEL Nanofil -R . Glibc \$< >$out/logs/\$(subst /,_,\$<).build 2>&1 || (echo "FAIL \$<"; exit 1)
include $out/deps
MK
if ! (cd "$tree" && make -k -j16 -f "$out/Makefile" $(printf '%s\n' $todo | sed 's/\.v$/.vo/')) >"$out/build.log" 2>&1; then
  echo "proof-using.sh: recompiling the rewritten files failed; see $out/build.log" >&2
  status=1
fi
printf '%s\n' $todo | xargs -P 16 -I{} bash -c 'query {} '"$out/after"
if grep -l '^Error:' "$out"/before/* "$out"/after/*; then
  echo "proof-using.sh: a type query failed" >&2
  status=1
elif ! diff -r "$out/before" "$out/after" >"$out/types.diff"; then
  echo "proof-using.sh: a declaration's type changed; see $out/types.diff" >&2
  status=1
fi
awk '{ n += $1 } END { print n " clauses in " NR " files" }' "$out/rewritten"
exit $status
