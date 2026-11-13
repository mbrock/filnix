#!/usr/bin/env bash
# The manifest owns this directory's units and functions.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
exec python3 -I "$here/../../scripts/glibc-code/generate.py" --directory hi_atexit "$@"
