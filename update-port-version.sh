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
INFO=$(./query-package.sh --full "$PKG" 2>/dev/null)

OLD_VERSION=$(echo "$INFO" | jq -r '.version')

# Get src URLs
URLS=$(echo "$INFO" | jq -r '.src.urls[]')

if [ -z "$URLS" ]; then
    echo "Error: No URLs found in package src" >&2
    exit 1
fi

# If version is the same, use existing hash
if [ "$OLD_VERSION" = "$NEW_VERSION" ]; then
    SRI_HASH=$(echo "$INFO" | jq -r '.src.hash')
    NEW_URL=$(echo "$URLS" | head -n1)
else
    # Replace version in first URL
    NEW_URL=$(echo "$URLS" | head -n1 | sed "s/$OLD_VERSION/$NEW_VERSION/g")

    # Prefetch the new URL
    PREFETCH_OUTPUT=$(nix store prefetch-file "$NEW_URL" 2>&1 || true)
    echo "$PREFETCH_OUTPUT" >&2

    if SRI_HASH=$(echo "$PREFETCH_OUTPUT" | grep -oP "sha256-[A-Za-z0-9+/=]+"); then
        : # Success
    else
        # Prefetch failed, use placeholder hash
        SRI_HASH="sha256-$(echo $RANDOM | sha256sum | cut -c1-52)==="
    fi
fi

cat <<EOF
source = {
  version = "$NEW_VERSION";
  hash = "$SRI_HASH";
  url = "$NEW_URL";
};
EOF
