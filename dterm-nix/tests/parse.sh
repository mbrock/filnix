#!/usr/bin/env bash
# parse.sh [FILE...]: nix_syntax reads each Nix file as Nix does. For each
# file (default: every .nix file in the repository), nix-instantiate
# --parse of the file and of tests/reprint.pl's fully parenthesized
# reprint of it must agree. Needs swipl and nix-instantiate on PATH.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../.."
[ $# -gt 0 ] || set -- $(git ls-files '*.nix')
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
ok=0 bad=0
for f in "$@"; do
  if ! nix-instantiate --parse - <"$f" >"$tmp/nix" 2>/dev/null; then
    echo "skip $f: nix-instantiate rejects it"; continue
  fi
  if swipl "$here/reprint.pl" "$f" "$tmp/re.nix" </dev/null 2>"$tmp/err" &&
    nix-instantiate --parse - <"$tmp/re.nix" >"$tmp/ours" 2>>"$tmp/err" &&
    cmp -s "$tmp/nix" "$tmp/ours"; then
    ok=$((ok + 1))
  else
    echo "FAIL $f"; head -3 "$tmp/err"; bad=$((bad + 1))
  fi
done
echo "parse.sh: $ok agree, $bad differ"
[ "$bad" -eq 0 ]
