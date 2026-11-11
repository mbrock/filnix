#!/usr/bin/env bash
# The two kernels of memcmp.ir under the poison spike: print the checked
# module nanofil -O makes of memcmp.ir as Gallina (MemcmpCode.v), compile
# the spike's Poison.v against the model's compiled theories, and
# compile MemcmpPoison.v, whose examples and theorem README.md
# describes.
#
#   ./poison.sh [POISON.v [WORKDIR]]
#
# POISON.v is nanofil/rocq/spikes/Poison.v unless named. Poison.v takes
# about five minutes to compile; a WORKDIR keeps its object for the next
# run. Needs nix. SWIPL names SWI-Prolog; without it nix builds the
# pinned one.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
poison=${1:-$repo/nanofil/rocq/spikes/Poison.v}
work=${2:-$(mktemp -d)}
if [ ! -e "$poison" ]; then
  echo "no $poison: name the spike's Poison.v" >&2
  exit 1
fi
poison=$(cd "$(dirname "$poison")" && pwd)/$(basename "$poison")
mkdir -p "$work/Spike" "$work/CtMemcmp"
cd "$work"

nixpkgs="(import (builtins.getFlake \"$repo\").inputs.nixpkgs { system = \"x86_64-linux\"; })"
export SWIPL=${SWIPL:-$(nix build --impure --no-link --print-out-paths --expr "$nixpkgs.swi-prolog" | head -1)/bin/swipl}
model="$repo#checks.x86_64-linux.nanofil-rocq.model"
theories=$(nix build --no-link --print-out-paths "$model.objects")/share/rocq/theories
compile() {
  nix develop "$model" -c rocq compile -R "$theories" Nanofil -R Spike Spike -R CtMemcmp CtMemcmp "$1"
}

(cd "$repo/nanofil/src" && ../bin/nanofil -O outcomes "$here/memcmp.ir" </dev/null) | grep '^module(' |
  (cd "$repo/nanofil" && "$SWIPL" rocq/scripts/gallina.pl memcmp experiments/ct-memcmp/memcmp.ir experiments/ct-memcmp/poison.sh) |
  sed 's#poison.sh checks it is$#poison.sh writes it, so it is#' >CtMemcmp/MemcmpCode.v
cp "$here/MemcmpPoison.v" CtMemcmp/

if ! cmp -s "$poison" Spike/Poison.v || [ ! -e Spike/Poison.vo ]; then
  cp "$poison" Spike/Poison.v
  echo "compiling Poison.v ($(sha256sum <Spike/Poison.v | cut -c1-16))"
  compile Spike/Poison.v
fi
compile CtMemcmp/MemcmpCode.v
compile CtMemcmp/MemcmpPoison.v | tee assumptions
[ "$(grep -c 'Closed under the global context' assumptions)" = 2 ] || {
  echo "FAIL: MemcmpPoison.v rests on an axiom" >&2
  exit 1
}
echo "ok: ct_memcmp is clean under the poison rules, for every content of the buffers; leaky_memcmp is caught"
