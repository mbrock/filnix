#!/usr/bin/env bash
# Compile one file of a glibc proof tree against the objects already
# built beside its imports. Extra arguments go to rocq, for example
# -time for a per-sentence profile.
#
#   . env.sh; one.sh TREE libio/LibioPutsNl.v [-time]
set -euo pipefail
tree=$1
file=$2
shift 2
cd "$tree"
exec rocq c -q -R "$PE_MODEL" Nanofil -R . Glibc "$@" "$file"
