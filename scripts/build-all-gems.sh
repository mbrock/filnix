#!/usr/bin/env bash
# Build native Ruby gems with nom output, save logs after

set -uo pipefail

RESULTS_DIR="${1:-gem-results}"
TIMEOUT="${2:-600}"  # 10 min default timeout per gem
mkdir -p "$RESULTS_DIR"

# Gems to skip (known incompatible)
SKIP_GEMS="opus-ruby taglib-ruby"

# Track if we should skip current build
SKIP=0
trap 'SKIP=1; echo " [skipping...]"' INT

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
echo "Timeout: ${TIMEOUT}s per gem"
echo "Ctrl-C to skip current gem, Ctrl-C twice to quit"
echo ""

SUCCESS=0
FAILED=0
SKIPPED=0
COUNT=0

for gem in $GEMS; do
    ((COUNT++)) || true
    SKIP=0

    # Skip if already done
    if [ -f "$RESULTS_DIR/$gem.ok.log" ] || [ -f "$RESULTS_DIR/$gem.fail.log" ]; then
        echo "[$COUNT/$TOTAL] $gem (cached)"
        continue
    fi

    # Skip known-bad gems
    if echo "$SKIP_GEMS" | grep -qw "$gem"; then
        echo "[$COUNT/$TOTAL] $gem (skip-listed)"
        continue
    fi

    echo ""
    echo "═══ [$COUNT/$TOTAL] $gem ═══"

    # Build with timeout, capture log during build
    LOG_FILE="$RESULTS_DIR/$gem.log"
    if timeout "$TIMEOUT" nix build ".#rubyWithGem.$gem" --no-link --log-format internal-json 2>&1 | tee "$LOG_FILE" | nom --json; then
        if [ "$SKIP" -eq 1 ]; then
            echo "⊘ $gem (skipped)"
            rm -f "$LOG_FILE"
            ((SKIPPED++)) || true
        else
            echo "✓ $gem"
            mv "$LOG_FILE" "$RESULTS_DIR/$gem.ok.log"
            ((SUCCESS++)) || true
        fi
    else
        EXIT_CODE=$?
        if [ "$SKIP" -eq 1 ] || [ "$EXIT_CODE" -eq 124 ]; then
            echo "⊘ $gem (skipped/timeout)"
            rm -f "$LOG_FILE"
            ((SKIPPED++)) || true
        else
            echo "✗ $gem"
            mv "$LOG_FILE" "$RESULTS_DIR/$gem.fail.log"
            ((FAILED++)) || true
        fi
    fi
done

echo ""
echo "═══════════════════════════════════════════"
echo "DONE: $SUCCESS ok, $FAILED failed, $SKIPPED skipped (of $TOTAL)"
echo "═══════════════════════════════════════════"
if ls "$RESULTS_DIR"/*.fail.log >/dev/null 2>&1; then
    echo "Failed:"
    ls "$RESULTS_DIR"/*.fail.log | xargs -n1 basename | sed 's/.fail.log//'
fi
