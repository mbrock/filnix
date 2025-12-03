#!/usr/bin/env bash
# Extract key errors from gem fail logs

RESULTS_DIR="${1:-gem-results}"

for f in "$RESULTS_DIR"/*.fail.log; do
    gem=$(basename "$f" .fail.log)
    echo "=== $gem ==="

    # Extract error lines from the embedded log in the msg field
    grep -o 'error:[^"]*' "$f" | head -3 | sed 's/\\n/\n/g; s/\\u001b\[[^m]*m//g'
    echo ""
done
