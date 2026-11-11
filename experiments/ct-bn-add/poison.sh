#!/usr/bin/env bash
# The three kernels lifted from bn_add.s under the poison spike
# (nanofil/rocq/spikes/Poison.v): print the checked module nanofil -O
# makes of the lifted IR as Gallina (BnAddCode.v), and compile
# BnAddPoison.v against it, whose examples and theorems README.md
# describes. Poison.v is compiled first, against the model's compiled
# theories.
#
#   ./poison.sh [WORKDIR]
#
# Poison.v takes about two minutes to compile; a WORKDIR keeps its
# object for the next run, and ../ct-memcmp/poison.sh can share it.
# Needs nix. SWIPL names SWI-Prolog; without it nix builds the pinned
# one.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
poison=$repo/nanofil/rocq/spikes/Poison.v
work=${1:-$(mktemp -d)}
mkdir -p "$work/Spike" "$work/CtBnAdd"
cd "$work"
work=$PWD

nixpkgs="(import (builtins.getFlake \"$repo\").inputs.nixpkgs { system = \"x86_64-linux\"; })"
export SWIPL=${SWIPL:-$(nix build --impure --no-link --print-out-paths --expr "$nixpkgs.swi-prolog" | head -1)/bin/swipl}
model="$repo#checks.x86_64-linux.nanofil-rocq.model"
theories=$(nix build --no-link --print-out-paths "$model.objects")/share/rocq/theories
compile() { nix develop "$model" -c rocq compile -R "$theories" Nanofil -R Spike Spike -R CtBnAdd CtBnAdd "$1"; }

if ! cmp -s "$poison" Spike/Poison.v || [ ! -e Spike/Poison.vo ]; then
  cp "$poison" Spike/Poison.v
  echo "compiling Poison.v ($(sha256sum <Spike/Poison.v | cut -c1-16))"
  compile Spike/Poison.v
fi

"$SWIPL" "$repo/experiments/ct-memcmp/lift/lift.pl" "$here/bn_add.s" >bn-lifted.ir
(cd "$repo/nanofil/src" && ../bin/nanofil -O outcomes "$work/bn-lifted.ir" </dev/null) | grep '^module(' |
  (cd "$repo/nanofil" && "$SWIPL" rocq/scripts/gallina.pl bn_add \
    "experiments/ct-bn-add/bn_add.s, lifted by experiments/ct-memcmp/lift/lift.pl" experiments/ct-bn-add/poison.sh) |
  sed 's#poison.sh checks it is$#poison.sh writes it, so it is#' >CtBnAdd/BnAddCode.v
cp "$here/BnAddPoison.v" CtBnAdd/
compile CtBnAdd/BnAddCode.v
compile CtBnAdd/BnAddPoison.v | tee assumptions
[ "$(grep -c 'Closed under the global context' assumptions)" = 3 ] || {
  echo "FAIL: BnAddPoison.v rests on an axiom" >&2
  exit 1
}
echo "ok: bn_add_words and bn_sub_words are clean under the poison rules, for every content of the operands;"
echo "    leaky_add_words is caught"
