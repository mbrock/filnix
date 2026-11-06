#!/usr/bin/env bash
# check-plan.sh I/N <LABELS: print the labels (one per line, in the
# Nix check's order) that shard I of N runs. Longest steps first, each
# to the shard with the least estimated time so far (ties to the lower
# shard); estimates are tests/check-times.tsv's "SECONDS<TAB>LABEL"
# lines, 60 s for a step not listed there. The split depends only on the
# labels and that file, so every shard of a commit computes the same
# one, and the N shards together list each label exactly once.
set -euo pipefail
case ${1-} in
  [1-9]*/[1-9]*) ;;
  *) echo "usage: check-plan.sh I/N <labels" >&2; exit 2 ;;
esac
i=${1%/*} n=${1#*/}
[ "$i" -le "$n" ] || { echo "check-plan.sh: shard $i of $n" >&2; exit 2; }
awk -F'\t' -v i="$i" -v n="$n" '
  FILENAME != "-" { if (NF == 2) est[$2] = $1; next }
  { m++; label[m] = $0; w[m] = ($0 in est) ? est[$0] : 60; order[m] = m }
  END {
    # Stable insertion sort of order[] by w, descending.
    for (a = 2; a <= m; a++) {
      x = order[a]
      for (b = a - 1; b >= 1 && w[order[b]] < w[x]; b--) order[b + 1] = order[b]
      order[b + 1] = x
    }
    for (s = 1; s <= n; s++) load[s] = 0
    for (a = 1; a <= m; a++) {
      best = 1
      for (s = 2; s <= n; s++) if (load[s] < load[best]) best = s
      load[best] += w[order[a]]
      mine[order[a]] = (best == i)
    }
    for (a = 1; a <= m; a++) if (mine[a]) print label[a]
  }' "$(dirname "$0")/check-times.tsv" -
