#!/usr/bin/env bash
# Build libpizlo's core for x86_64-pc-serenity and report what it needs.
#
# Takes the pinned libpas source, applies libpas-serenity.patch, generates the
# native forwarders, splits the Linux syscall layer out with split_zsys.py, and
# gives Serenity an empty syscall backend. It then compiles every libpizlo
# source with clang's Serenity target against Serenity's LibC headers, at
# libpizlo's own flags (-O3 -W -Werror), links the objects into one shared
# object, and sorts its undefined symbols into syscall natives still to write,
# functions Serenity's LibC implements, and anything else.
#
# Usage: serenity-core.sh SERENITY_CHECKOUT WORKDIR
set -euo pipefail

S=$1
work=$2
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
nix() { command nix --extra-experimental-features 'nix-command flakes' "$@"; }

libpas=$(nix eval --raw "$repo#filcc.sources.libpas-src")
paths=$(nix build --no-link --print-out-paths --inputs-from "$repo" \
  nixpkgs#llvmPackages_20.clang-unwrapped nixpkgs#llvmPackages_20.clang-unwrapped.lib \
  nixpkgs#binutils-unwrapped nixpkgs#ruby)
clang=$(grep -E -- '-clang-[0-9.]+$' <<<"$paths")/bin/clang
res=$(grep -E -- '-clang-[0-9.]+-lib$' <<<"$paths")/lib/clang/20
ld=$(grep -E -- '-binutils-[0-9.]+$' <<<"$paths")/bin/ld.bfd
ruby=$(grep -E -- '-ruby-' <<<"$paths")/bin/ruby

rm -rf "$work/libpas" "$work/obj"
mkdir -p "$work/obj"
cp -r --no-preserve=mode "$libpas" "$work/libpas"
cd "$work/libpas"
patch -p1 -s <"$here/libpas-serenity.patch"
cd libpas
"$ruby" src/libpas/generate_pizlonated_forwarders.rb src/libpas/filc_native.h
"$ruby" src/libpas/generate_pizlonated_forwarders.rb src/libpas/filc_native_forwarders.c
python3 "$here/split_zsys.py" src/libpas
: >src/libpas/filc_zsys_serenity.c

srcs=$(sed -n '/^PASSRCS = /,/^$/p' common.mk | grep -o 'src/libpas/[a-z_0-9]*\.c')
srcs="$srcs src/libpas/filc_dynamic.c src/libpas/filc_default_settings.c"
failed=0
for f in $srcs; do
  if ! "$clang" -resource-dir "$res" --target=x86_64-pc-serenity -fPIC -pthread -nostdinc \
      -isystem "$res/include" -isystem "$S/Userland/Libraries/LibC" -isystem ../filc/include \
      -I"$S" -I"$S/Userland/Libraries" -D__serenity__ -D__unix__ \
      -g -O3 -W -Werror -fno-strict-aliasing -DPAS_FILC=1 \
      -c "$f" -o "$work/obj/$(basename "$f" .c).o" 2>"$work/err.log"; then
    failed=$((failed + 1))
    echo "$f: $(grep -m1 'error:' "$work/err.log")"
  fi
done
"$clang" --target=x86_64-pc-serenity -c src/libpas/filc_stack_overflow_failure.S -o "$work/obj/filc_stack_overflow_failure.o"
echo "objects: $(ls "$work/obj" | wc -l), failed: $failed"
[ "$failed" = 0 ]

"$ld" -shared -o "$work/libpizlo-serenity-core.so" "$work"/obj/*.o
nm -u "$work/libpizlo-serenity-core.so" | awk '{print $2}' | sort -u >"$work/undefined.txt"
L=$S/Userland/Libraries
natives=0 libc=0 other=""
while read -r sym; do
  case $sym in
  filc_native_zsys_*) natives=$((natives + 1)) ;;
  __cpu_model | __cpu_features2 | __cpu_indicator_init) other="$other $sym(compiler-rt)" ;;
  *)
    if grep -rqE "(^|[ *(])$sym\s*\(|\b$sym\b\s*(=|;|\[)|MAKE_AK_BACKED[0-9]\(${sym%[lf]}\)|^\.global $sym$" \
        --include=*.cpp --include=*.S "$L/LibC" "$L/LibELF" 2>/dev/null; then
      libc=$((libc + 1))
    else
      other="$other $sym"
    fi
    ;;
  esac
done <"$work/undefined.txt"
echo "undefined: $(wc -l <"$work/undefined.txt") = $natives syscall natives for the Serenity backend + $libc implemented by Serenity LibC + other:${other:- none}"
