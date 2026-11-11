#!/usr/bin/env bash
# The two kernels under the poison spike (nanofil/rocq/spikes/Poison.v),
# once as the hand translation memcmp.ir and once as lift/lift.pl lifts
# them from memcmp.s. For each: print the checked module nanofil -O
# makes of the IR as Gallina (MemcmpCode.v), and compile MemcmpPoison.v
# against it, whose examples and theorem README.md describes. Poison.v
# is compiled first, against the model's compiled theories.
#
#   ./poison.sh [WORKDIR]
#
# Poison.v takes about two minutes to compile; a WORKDIR keeps its
# object for the next run. Needs nix. SWIPL names SWI-Prolog; without it
# nix builds the pinned one.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
poison=$repo/nanofil/rocq/spikes/Poison.v
work=${1:-$(mktemp -d)}
mkdir -p "$work/Spike"
cd "$work"
work=$PWD

nixpkgs="(import (builtins.getFlake \"$repo\").inputs.nixpkgs { system = \"x86_64-linux\"; })"
export SWIPL=${SWIPL:-$(nix build --impure --no-link --print-out-paths --expr "$nixpkgs.swi-prolog" | head -1)/bin/swipl}
model="$repo#checks.x86_64-linux.nanofil-rocq.model"
theories=$(nix build --no-link --print-out-paths "$model.objects")/share/rocq/theories
compile() { # compile DIR FILE: FILE with DIR/CtMemcmp as the library CtMemcmp
  nix develop "$model" -c rocq compile -R "$theories" Nanofil -R Spike Spike -R "$1/CtMemcmp" CtMemcmp "$2"
}

if ! cmp -s "$poison" Spike/Poison.v || [ ! -e Spike/Poison.vo ]; then
  cp "$poison" Spike/Poison.v
  echo "compiling Poison.v ($(sha256sum <Spike/Poison.v | cut -c1-16))"
  compile . Spike/Poison.v
fi

check() { # check NAME IR SOURCE: the checked module of IR under the spike
  mkdir -p "$1/CtMemcmp"
  (cd "$repo/nanofil/src" && ../bin/nanofil -O outcomes "$2" </dev/null) | grep '^module(' |
    (cd "$repo/nanofil" && "$SWIPL" rocq/scripts/gallina.pl memcmp "$3" experiments/ct-memcmp/poison.sh) |
    sed 's#poison.sh checks it is$#poison.sh writes it, so it is#' >"$1/CtMemcmp/MemcmpCode.v"
  cp "$here/MemcmpPoison.v" "$1/CtMemcmp/"
  compile "$1" "$1/CtMemcmp/MemcmpCode.v"
  compile "$1" "$1/CtMemcmp/MemcmpPoison.v" | tee "$1/assumptions"
  [ "$(grep -c 'Closed under the global context' "$1/assumptions")" = 2 ] || {
    echo "FAIL: MemcmpPoison.v rests on an axiom for the $1 IR" >&2
    exit 1
  }
  echo "ok ($1): ct_memcmp is clean under the poison rules, for every content of the buffers; leaky_memcmp is caught"
}
check hand "$here/memcmp.ir" experiments/ct-memcmp/memcmp.ir
"$SWIPL" "$here/lift/lift.pl" "$here/memcmp.s" >lifted.ir
check lifted "$work/lifted.ir" "experiments/ct-memcmp/memcmp.s, lifted by lift/lift.pl"
