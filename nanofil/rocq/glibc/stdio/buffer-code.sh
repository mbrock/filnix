#!/usr/bin/env bash
# The unified stdio manifest now also owns the buffer fixtures.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
exec "$here/code.sh" "$@"
