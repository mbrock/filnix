#!/usr/bin/env bash
# Check all manifests, or regenerate with --update. Use --legacy before cutover.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
exec python3 -I "$here/../scripts/glibc-code/generate.py" "$@"
