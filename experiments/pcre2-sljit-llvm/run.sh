#!/usr/bin/env bash
# Rebuild and run the sljit-to-LLVM replay prototype.
#
#   ./run.sh            build everything under $WORK, then run all patterns
#   ./run.sh dump       also regenerate lir/*.txt from the native build
#
# Needs gcc, make, curl and nix. The Fil-C side uses the staging toolchain,
# because the release one has no LLVM JIT.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
WORK=${WORK:-/tmp/pcre2-sljit-llvm}
BUDGET=${BUDGET:-0.3}
OPT=${OPT:-2}
version=10.49
sha256=53c156e1ba416a20da8e65395daa132da0d80e76910424caca3fcdae7831d384
patterns="tag email word alt entity shortcode key date utf lit"

mkdir -p "$WORK"
cd "$WORK"

if [ ! -d pcre2-$version ]; then
  curl -fsSL -o pcre2.tar.bz2 \
    "https://github.com/PCRE2Project/pcre2/releases/download/pcre2-$version/pcre2-$version.tar.bz2"
  echo "$sha256  pcre2.tar.bz2" | sha256sum -c -
  tar xf pcre2.tar.bz2
fi
if [ ! -d pcre2-dump ]; then
  cp -r pcre2-$version pcre2-dump
  patch -d pcre2-dump -p1 <"$here/sljit-dump.patch"
fi
if [ ! -d pcre2-match ]; then
  cp -r pcre2-$version pcre2-match
  patch -d pcre2-match -p1 <"$repo/patches/pcre2-10.48-filc-match.patch"
fi

[ -e filcc-staging ] || nix build "$repo#filcc-staging" -o filcc-staging
filcc=$WORK/filcc-staging/bin/clang

# build NAME SOURCE CONFIGURE-ARGS...: a static libpcre2-8 in build/NAME.
build() {
  local name=$1 src=$2
  shift 2
  [ -e "build/$name/.libs/libpcre2-8.a" ] && return
  mkdir -p "build/$name"
  (cd "build/$name" && "$WORK/$src/configure" --disable-shared "$@" >configure.log &&
    make -j"$(nproc)" libpcre2-8.la >make.log 2>&1)
}

# Native sljit without the SIMD fast-forward paths: the baseline, and the
# source of the LIR dumps.
build native-nosimd pcre2-dump --enable-jit CC=gcc "CFLAGS=-O2 -DPROTO_NO_SIMD"
# Fil-C interpreter, as upstream and with the match patch PHP uses.
build filc-nojit pcre2-$version --disable-jit CC="$filcc" CFLAGS=-O2
build filc-match pcre2-match --disable-jit CC="$filcc" CFLAGS=-O2

bench() { # bench OUTPUT CC BUILD
  "$2" -O2 -I"build/$3/src" -I"$here" "$here/bench.c" "build/$3/.libs/libpcre2-8.a" -o "$1"
}
bench bench-native-nosimd gcc native-nosimd
bench bench-filc-nojit "$filcc" filc-nojit
bench bench-filc-match "$filcc" filc-match

# The replay reads pcre2_real_code and pcre2_match_data directly, at the
# offsets the native LIR hard-codes, so it links the unpatched library.
"$filcc" -O2 -g -enable-filc-jit -DHAVE_CONFIG_H -Ibuild/filc-nojit/src -Ipcre2-$version/src \
  -I"$here" "$here/replay.c" build/filc-nojit/.libs/libpcre2-8.a -o replay

if [ "${1:-}" = dump ]; then
  for p in $patterns; do
    SLJIT_DUMP=1 ./bench-native-nosimd jit 0.01 "$p" 2>"$here/lir/$p.txt" >/dev/null
  done
fi

echo "== native sljit, no SIMD"
./bench-native-nosimd jit "$BUDGET"
echo "== Fil-C interpreter"
./bench-filc-nojit x "$BUDGET"
echo "== Fil-C interpreter with pcre2-10.48-filc-match.patch"
./bench-filc-match x "$BUDGET"
echo "== Fil-C LLVM JIT (replayed sljit LIR) against the Fil-C interpreter"
cd "$here"
for p in $patterns; do
  "$WORK/replay" "$p" "$OPT" "$BUDGET"
done
