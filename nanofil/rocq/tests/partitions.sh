#!/usr/bin/env bash
# Partitioning must neither drop nor duplicate any verdict, including
# data/alias mutants and inserted items. Compare the public stream, not
# the implementation's item-selection predicate.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export LC_ALL=C
cd "$here/../src"
../bin/nanofil cc-ir ../tests/c/prog/alias.c >"$work/alias.ir" </dev/null
../bin/nanofil outcomes "$work/alias.ir" >"$work/out" </dev/null
NANOFIL_STATE= ../bin/nanofil --script ../rocq/scripts/mutants.pl <"$work/out" >"$work/reference"
head -1 "$work/reference" >"$work/module"
tail -n +2 "$work/reference" | sort >"$work/verdicts"
test -s "$work/verdicts"
for shard in 0 1 2; do
  NANOFIL_STATE= ../bin/nanofil --script ../rocq/scripts/mutants.pl "$shard" 3 \
    <"$work/out" >"$work/part-$shard"
  head -1 "$work/part-$shard" | cmp - "$work/module"
  tail -n +2 "$work/part-$shard"
done | sort >"$work/partitioned"
cmp "$work/verdicts" "$work/partitioned"
echo "mutant partitions: $(wc -l <"$work/verdicts") verdicts, exactly once"
NANOFIL_STATE= ../bin/nanofil --script ../rocq/scripts/mutants.pl --base <"$work/out" >"$work/base"
head -1 "$work/base" | cmp - "$work/module"
grep -E '^verdict\([^,]+,[0-9]+,base,' "$work/reference" >"$work/expected-base"
test -s "$work/expected-base"
tail -n +2 "$work/base" | cmp - "$work/expected-base"
echo "base-only: $(wc -l <"$work/expected-base") unchanged verdicts, no mutants"
