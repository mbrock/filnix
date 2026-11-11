#!/usr/bin/env bash
# Reuse the existing NASM-to-SaRCAsm pipeline with each isolated assembler.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
work=${1:?usage: build-jpeg.sh WORKDIR}
mkdir -p "$work"
work=$(realpath "$work")
expr=$here/default.nix
build() { nix build --impure -f "$expr" "$1" --no-link --print-out-paths; }
export FILC_CC=$(build filcc)/bin/clang
export REAL_NASM=$(build pkgs.nasm)/bin/nasm
cmake=$(build pkgs.cmake)/bin
src=$(build pkgs.libjpeg_turbo.src)
cp -R "$src" "$work/src"
chmod -R u+w "$work/src"
patch -d "$work/src" -p1 < "$repo/ports/patch/libjpeg-turbo-3.0.1.patch"
patch -d "$work/src" -p1 < "$repo/experiments/libjpeg-turbo-sarcasm/libjpeg-turbo-sarcasm.patch"
result=0
for variant in before after; do
    if [ "$variant" = before ]; then asm=oldAssembler; else asm=newAssembler; fi
    export SARCASM=$(build "$asm")
    "$cmake/cmake" -S "$work/src" -B "$work/$variant" \
        -DCMAKE_C_COMPILER="$FILC_CC" -DCMAKE_BUILD_TYPE=Release \
        -DENABLE_STATIC=0 -DWITH_JAVA=0 -DREQUIRE_SIMD=1 \
        -DCMAKE_ASM_NASM_COMPILER="$repo/experiments/libjpeg-turbo-sarcasm/filc-nasm" \
        -DFLOATTEST8=no-fp-contract
    "$cmake/cmake" --build "$work/$variant" -j6
    # Record all results, including the experiment's documented float failures.
    if "$cmake/ctest" --test-dir "$work/$variant" -j6 --output-on-failure \
        > "$work/$variant-tests.log" 2>&1; then
        echo 0 > "$work/$variant-tests.exit"
    else
        result=$?
        echo "$result" > "$work/$variant-tests.exit"
        echo "$variant tests failed; see $work/$variant-tests.log" >&2
    fi
done
exit "$result"
