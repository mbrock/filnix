#!/usr/bin/env bash
# Build libjpeg-turbo for Fil-C with its x86-64 NASM SIMD assembled by
# SaRCAsm, then run its test suite.
#
# usage: experiments/libjpeg-turbo-sarcasm/run.sh WORKDIR
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
work=${1:?usage: run.sh WORKDIR}
mkdir -p "$work"
work=$(cd "$work" && pwd)

nixpkgs="(import (builtins.getFlake \"$repo\").inputs.nixpkgs { system = \"x86_64-linux\"; })"
build() { nix build --impure --no-link --print-out-paths --expr "$1" | head -1; }
export REAL_NASM=$(build "$nixpkgs.nasm")/bin/nasm
export FILC_CC=$(nix build --no-link --print-out-paths "$repo#filcc")/bin/clang
export SARCASM=$(nix build --no-link --print-out-paths "$repo#sarcasm")
cmake=$(build "$nixpkgs.cmake")/bin
src=$(build "$nixpkgs.libjpeg_turbo.src")

rm -rf "$work/src" "$work/build"
cp -r "$src" "$work/src"
chmod -R u+w "$work/src"
patch -d "$work/src" -p1 < "$repo/ports/patch/libjpeg-turbo-3.0.1.patch"
patch -d "$work/src" -p1 < "$here/libjpeg-turbo-sarcasm.patch"

mkdir -p "$work/tmp"
export TMPDIR=$work/tmp
CC=$FILC_CC "$cmake/cmake" -S "$work/src" -B "$work/build" \
  -DCMAKE_BUILD_TYPE=Release -DENABLE_STATIC=0 -DWITH_JAVA=0 \
  -DREQUIRE_SIMD=1 -DCMAKE_ASM_NASM_COMPILER="$here/filc-nasm" \
  -DFLOATTEST8=no-fp-contract
"$cmake/cmake" --build "$work/build" -j"$(nproc)"
cd "$work/build" && "$cmake/ctest" -j"$(nproc)" --output-on-failure
