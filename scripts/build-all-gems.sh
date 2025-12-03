#!/usr/bin/env bash
# Build native Ruby gems with nom output, save logs after

set -uo pipefail

# Handle Ctrl-C gracefully
trap 'echo ""; echo "Interrupted!"; exit 130' INT

RESULTS_DIR="${1:-gem-results}"
mkdir -p "$RESULTS_DIR"

# Get native gems only (the ones with C extensions)
GEMS=$(nix eval --raw --impure --expr '
  let
    pkgs = import <nixpkgs> {};
    rubyports = import ./rubyports.nix { inherit pkgs; };
  in builtins.toJSON (builtins.concatLists (builtins.attrValues rubyports.nativeGems))
' 2>/dev/null | jq -r '.[]')

TOTAL=$(echo "$GEMS" | wc -l)
echo "Building $TOTAL native gems (with C extensions)"
echo "Results: $RESULTS_DIR/"
echo "Press Ctrl-C to stop"
echo ""

SUCCESS=0
FAILED=0
COUNT=0

for gem in $GEMS; do
    ((COUNT++)) || true
    echo ""
    echo "═══ [$COUNT/$TOTAL] $gem ═══"

    # Build with nom for nice output
    if nom build ".#rubyWithGem.$gem" --no-link 2>&1; then
        echo "✓ $gem"
        nix log ".#rubyWithGem.$gem" > "$RESULTS_DIR/$gem.ok.log" 2>/dev/null || true
        ((SUCCESS++)) || true
    else
        echo "✗ $gem"
        nix log ".#rubyWithGem.$gem" > "$RESULTS_DIR/$gem.fail.log" 2>/dev/null || true
        ((FAILED++)) || true
    fi
done

echo ""
echo "═══════════════════════════════════════════"
echo "DONE: $SUCCESS ok, $FAILED failed (of $TOTAL)"
echo "═══════════════════════════════════════════"
if ls "$RESULTS_DIR"/*.fail.log >/dev/null 2>&1; then
    echo "Failed:"
    ls "$RESULTS_DIR"/*.fail.log | xargs -n1 basename | sed 's/.fail.log//'
fi
