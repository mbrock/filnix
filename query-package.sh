#!/usr/bin/env bash
# Query package information from nixpkgs (using flake's pinned version)
# Usage: ./query-package.sh [--full] PACKAGE_NAME

set -euo pipefail

FULL=false
PACKAGE=""

while [[ $# -gt 0 ]]; do
    case $1 in
        --full)
            FULL=true
            shift
            ;;
        *)
            PACKAGE="$1"
            shift
            ;;
    esac
done

if [ -z "$PACKAGE" ]; then
    echo "Usage: $0 [--full] PACKAGE_NAME" >&2
    echo "Example: $0 bash" >&2
    echo "        $0 --full bash" >&2
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

INFO=$(nix eval --json .#lib.x86_64-linux.queryPackage --apply "f: f \"$PACKAGE\"" 2>/dev/null)

if [ "$FULL" = true ]; then
    echo "$INFO" | jq .
else
    # Print formatted synopsis
    echo "$INFO" | jq -r '
      def section(name; content): 
        if (content | length) > 0 then
          "\n\(name):\n\(content)"
        else
          ""
        end;
      
      # Collect all dependency names from build inputs
      def allDeps:
        [
          (.buildInputs.native[]? | select(. != null) | .name // .pname),
          (.buildInputs.build[]? | select(. != null) | .name // .pname),
          (.buildInputs.propagated[]? | select(. != null) | .name // .pname)
        ];
      
      def nativeInputs:
        (.buildInputs.native | map(select(. != null) | "  \(.name // .pname)") | join("\n"));
      
      def buildInputs:
        (.buildInputs.build | map(select(. != null) | "  \(.name // .pname)") | join("\n"));
      
      def propagatedInputs:
        (.buildInputs.propagated | map(select(. != null) | "  \(.name // .pname)") | join("\n"));
      
      def flags:
        [
          (if .buildConfig.configureFlags != [] then "  configureFlags: \(.buildConfig.configureFlags | join(" "))" else empty end),
          (if .buildConfig.makeFlags != [] then "  makeFlags: \(.buildConfig.makeFlags | join(" "))" else empty end),
          (if .buildConfig.cmakeFlags != [] then "  cmakeFlags: \(.buildConfig.cmakeFlags | join(" "))" else empty end)
        ] | join("\n");
      
      def args:
        . as $root |
        allDeps as $deps |
        [
          ($root.functionArgs.required[]? | select(. as $arg | $deps | contains([$arg]) | not) | "  \(.)"),
          ($root.functionArgs.optional[]? | select(. as $arg | $deps | contains([$arg]) | not) | "  \(.) (optional)")
        ] | join("\n");
      
      def patches:
        (.buildConfig.patches | map(sub("/nix/store/[^/]+-source/"; "$nixpkgs/") | "  \(.)") | join("\n"));
      
      [
        "Package: \(.pname // .name)\nVersion: \(.version)",
        section("Function Arguments"; args),
        section("Native Build Inputs"; nativeInputs),
        section("Build Inputs"; buildInputs),
        section("Propagated Build Inputs"; propagatedInputs),
        section("Build Flags"; flags),
        section("Patches"; patches)
      ] | map(select(length > 0)) | join("\n")
    '
fi
