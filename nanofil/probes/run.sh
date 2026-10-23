#!/usr/bin/env bash
# Regenerate the ABI probes against the pinned Fil-C and run the link test.
# Usage: nanofil/probes/run.sh [outdir]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=${1:-$(mktemp -d)}
mkdir -p "$out"
filcc=$(nix build "$here/../..#filcc" --no-link --print-out-paths)
cc="$filcc/bin/clang"

for p in abi abi2; do
  "$cc" -O2 -S -emit-llvm "$here/$p.c" -o "$out/$p.ll"
  "$cc" -O2 -S "$here/$p.c" -o "$out/$p.s"
done

as "$here/link/add2.s" -o "$out/add2.o"
"$cc" -O2 "$here/link/main.c" "$out/add2.o" -o "$out/link-test"
# The wrong-signature call must reach our generic entry and panic.
set +e
"$out/link-test" >"$out/link-test.out" 2>&1
status=$?
set -e
grep -q '^direct 42 indirect 1337$' "$out/link-test.out"
grep -q 'argument size mismatch (actual = 8, expected = 16)' "$out/link-test.out"
test "$status" -ne 0
echo "probes ok: $out"
