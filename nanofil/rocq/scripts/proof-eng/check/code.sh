#!/usr/bin/env bash
# Check generated fixtures against a proof tree where the capture is available.
# Usage: code.sh CAPTURE STAGED_TREE
# The Nix caller supplies filcc (FILCC), SWI-Prolog (SWIPL) and Python 3.11+.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
capture=${1:?pass the glibc capture directory}
tree=${2:?pass the glibc proof tree}
shift 2
exec python3 -I "$here/../../glibc-code/generate.py" "$capture" --tree "$tree" --form shared-prelude "$@"
