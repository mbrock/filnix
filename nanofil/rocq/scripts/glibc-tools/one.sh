#!/usr/bin/env bash
# Compile one file of a glibc proof tree against the objects already
# built beside its imports. Extra arguments go to rocq, for example
# -time for a per-sentence profile. With PE_THEORIES=1 (env.sh), TREE
# can also be the checkout's theories, PE_MODEL itself.
#
#   . env.sh; one.sh TREE libio/LibioPutsNl.v [-time]
#   PE_THEORIES=1 . env.sh; one.sh nanofil/rocq/theories exec/AbsSound.v
set -euo pipefail
tree=$(cd "$1" && pwd)
file=$2
shift 2
cd "$tree"
if [ "$tree" = "$(cd "$PE_MODEL" && pwd)" ]; then
  exec rocq c -q -R . Nanofil "$@" "$file"
fi
exec rocq c -q -R "$PE_MODEL" Nanofil -R . Glibc "$@" "$file"
