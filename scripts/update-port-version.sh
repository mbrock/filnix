#!/usr/bin/env bash
set -euo pipefail

if [ $# -ne 2 ]; then
    echo "Usage: $0 <package-name> <new-version>"
    echo "Example: $0 zlib 1.3.2"
    exit 1
fi

PKG="$1"
NEW_VERSION="$2"

# Get current package info
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
INFO=$("$SCRIPT_DIR/query-package.sh" --full "$PKG" 2>/dev/null)

OLD_VERSION=$(echo "$INFO" | jq -r '.version')

# Get src URLs
FIRST_URL=$(echo "$INFO" | jq -r '.src.urls[0] // empty')

if [ -z "$FIRST_URL" ]; then
    echo "Error: No URLs found in package src" >&2
    exit 1
fi

# If version is the same, use existing hash
if [ "$OLD_VERSION" = "$NEW_VERSION" ]; then
    SRI_HASH=$(echo "$INFO" | jq -r '.src.hash')
    NEW_URL="$FIRST_URL"
else
    # Replace version in first URL
    NEW_URL="${FIRST_URL//"$OLD_VERSION"/"$NEW_VERSION"}"
    if [ "$NEW_URL" = "$FIRST_URL" ]; then
        echo "Error: Source URL does not contain version $OLD_VERSION; provide a custom source URL" >&2
        exit 1
    fi

    # Prefetch the new URL
    PREFETCH_OUTPUT=$(nix store prefetch-file --json "$NEW_URL")
    SRI_HASH=$(echo "$PREFETCH_OUTPUT" | jq -er '.hash')
fi

cat <<EOF
source = {
  version = "$NEW_VERSION";
  hash = "$SRI_HASH";
  url = "$NEW_URL";
};
EOF
