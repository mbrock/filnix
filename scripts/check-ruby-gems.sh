#!/usr/bin/env bash
# Check which Ruby gems build under Fil-C and collect failure logs

set -euo pipefail

RESULTS_DIR="${1:-./gem-results}"
mkdir -p "$RESULTS_DIR/logs"

# Get all native gem names from rubyports.nix
GEMS=$(nix eval --raw --impure --expr '
  let
    pkgs = import <nixpkgs> {};
    rubyPorts = import ./rubyports.nix { inherit pkgs; };
    allGems = pkgs.lib.flatten (builtins.attrValues rubyPorts.nativeGems);
  in builtins.concatStringsSep "\n" allGems
')

echo "Checking $(echo "$GEMS" | wc -l) native gems..."
echo

passed=()
failed=()
skipped=()

for gem in $GEMS; do
  printf "%-25s " "$gem"

  # Check if gem exists in pkgsFilc
  if ! nix eval ".#pkgsFilc.ruby_3_3.gems.${gem}" &>/dev/null 2>&1; then
    echo "SKIP (not in nixpkgs)"
    skipped+=("$gem")
    continue
  fi

  # Try to build
  log_file="$RESULTS_DIR/logs/${gem}.log"
  if nix build ".#pkgsFilc.ruby_3_3.gems.${gem}" --no-link 2>"$log_file"; then
    echo "OK"
    passed+=("$gem")
    rm -f "$log_file"  # Remove log for successful builds
  else
    echo "FAIL"
    failed+=("$gem")
    # Get full nix log if available
    drv=$(nix eval --raw ".#pkgsFilc.ruby_3_3.gems.${gem}.drvPath" 2>/dev/null || true)
    if [[ -n "$drv" ]]; then
      nix log "$drv" >> "$log_file" 2>/dev/null || true
    fi
  fi
done

echo
echo "=== Summary ==="
echo "Passed:  ${#passed[@]}"
echo "Failed:  ${#failed[@]}"
echo "Skipped: ${#skipped[@]}"

# Write summary files
printf '%s\n' "${passed[@]}" > "$RESULTS_DIR/passed.txt" 2>/dev/null || touch "$RESULTS_DIR/passed.txt"
printf '%s\n' "${failed[@]}" > "$RESULTS_DIR/failed.txt" 2>/dev/null || touch "$RESULTS_DIR/failed.txt"
printf '%s\n' "${skipped[@]}" > "$RESULTS_DIR/skipped.txt" 2>/dev/null || touch "$RESULTS_DIR/skipped.txt"

echo
echo "Results written to $RESULTS_DIR/"
echo "  passed.txt  - gems that built successfully"
echo "  failed.txt  - gems that failed to build"
echo "  skipped.txt - gems not found in nixpkgs"
echo "  logs/       - build logs for failed gems"

if [[ ${#failed[@]} -gt 0 ]]; then
  echo
  echo "Failed gems:"
  printf '  %s\n' "${failed[@]}"
fi
