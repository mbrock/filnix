#!/usr/bin/env bash
# Compile the bytecode pcre2_compile makes of the patterns in
# ../pcre2-sljit-llvm/pats.h and more.h with rx.pl and nanofil, load the
# result into a Fil-C program, and compare it with PCRE2's interpreter.
# Then build a libpcre2 with the hook (pcre2-rx-hook.patch), which does
# the same per pattern behind pcre2_jit_compile and pcre2_match, and run
# hook.c against it with an empty cache and again with the full one.
#
#   ./run.sh              all patterns in one shared object, then the hook
#   HOST=tpl ./run.sh     regex to IR on Trealla instead of SWI-Prolog
#
# Needs nix, GNU as, and the PCRE2 source and Fil-C build that
# ../pcre2-sljit-llvm/run.sh leaves in $WORK. SWIPL and TPL name the
# Prolog hosts; without them nix builds the pinned ones.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
WORK=${WORK:-/tmp/pcre2-sljit-llvm}
OUT=${OUT:-$WORK/regex-nanofil}
BUDGET=${BUDGET:-0.3}
HOST=${HOST:-swi}
pcre2=$WORK/build/filc-nojit
src=$WORK/pcre2-10.49 # the version ../pcre2-sljit-llvm/run.sh fetches

if [ ! -e "$pcre2/.libs/libpcre2-8.a" ]; then
  echo "run ../pcre2-sljit-llvm/run.sh first: no $pcre2" >&2
  exit 1
fi
mkdir -p "$OUT"
cd "$OUT"

nixpkgs="(import (builtins.getFlake \"$repo\").inputs.nixpkgs { system = \"x86_64-linux\"; })"
if [ -z "${SWIPL:-}" ]; then
  [ -e swipl ] || nix build --impure --expr "$nixpkgs.swi-prolog" -o swipl
  SWIPL=$OUT/swipl/bin/swipl
fi
if [ "$HOST" = tpl ] && [ -z "${TPL:-}" ]; then
  [ -e tpl ] || nix build --impure --expr "import $repo/nanofil/nix/trealla.nix { pkgs = $nixpkgs; }" -o tpl
  TPL=$OUT/tpl/bin/tpl
fi
filcc=$WORK/filcc-staging/bin/clang
export SWIPL

# What pcre2_compile made of each pattern, as Prolog terms.
"$filcc" -O2 -DHAVE_CONFIG_H -I"$pcre2/src" -I"$src/src" -I"$here/../pcre2-sljit-llvm" \
  -o dump "$here/dump.c" "$pcre2/.libs/libpcre2-8.a"
./dump >pats.pl

step() { # step LABEL COMMAND...: run it and say how long it took
  local label=$1 t0 t1
  shift
  t0=$(date +%s%N)
  "$@"
  t1=$(date +%s%N)
  printf '%-28s %5d ms\n' "$label" $(((t1 - t0) / 1000000))
}

regex_to_ir() {
  case $HOST in
    swi) "$SWIPL" -q -g "consult('$here/rx.pl'), rx:rx_file('pats.pl')" -t halt \
      "$repo/nanofil/src/swi/compat.pl" </dev/null >rx.ir ;;
    tpl) "$TPL" -q "$here/rx.pl" -g "rx:rx_file('pats.pl')" -g halt </dev/null >rx.ir ;;
  esac
}
ir_to_asm() {
  (cd "$repo/nanofil/src" && NANOFIL_STATE=$OUT/nanofil.state ../bin/nanofil -O compile "$OUT/rx.ir" </dev/null) >rx.s
}

[ -e nanofil.state ] || "$repo/nanofil/bin/nanofil" --save-state "$OUT/nanofil.state"
step "regex to IR ($HOST)" regex_to_ir
grep '^%' rx.ir || true
step "nanofil -O compile (swi)" ir_to_asm
step "as" as -o rx.o rx.s
step "link -shared" "$filcc" -shared -o rx.so rx.o

"$filcc" -O2 -I"$pcre2/src" -I"$here/../pcre2-sljit-llvm" -o bench "$here/bench.c" "$pcre2/.libs/libpcre2-8.a"
./bench ./rx.so "$BUDGET"

# The hook: PCRE2 with the match patch, the hook patch and its two headers.
if [ ! -d "$WORK/pcre2-rx" ]; then
  cp -r "$WORK/pcre2-match" "$WORK/pcre2-rx"
  patch -d "$WORK/pcre2-rx" -p1 <"$here/pcre2-rx-hook.patch"
fi
cp "$here/pcre2_rx_inc.h" "$here/pcre2_rx_terms.h" "$WORK/pcre2-rx/src/"
hooked=$WORK/build/filc-rx
mkdir -p "$hooked"
(cd "$hooked" &&
  { [ -e Makefile ] || "$WORK/pcre2-rx/configure" --disable-shared --disable-jit CC="$filcc" CFLAGS=-O2 >configure.log; } &&
  make -j"$(nproc)" libpcre2-8.la >make.log 2>&1)
"$filcc" -O2 -I"$hooked/src" -I"$here/../pcre2-sljit-llvm" -I"$here" -o hook "$here/hook.c" "$hooked/.libs/libpcre2-8.a"

rm -rf cache
mkdir -m 755 cache
export PCRE2_RX_CACHE=$OUT/cache NANOFIL_STATE=$OUT/nanofil.state
echo "empty cache:"
PCRE2_RX_COMPILER=$here/rxc ./hook "$BUDGET"
echo "full cache, no compiler:"
./hook 0 | tail -n 1
