#!/usr/bin/env bash
# OpenSSL's bn_add_words and bn_sub_words carry loops and a control that
# branches on the carry, three ways: as plain assembly called unchecked,
# as the same assembly through SaRCAsm, and as the nanofil IR that
# ../ct-memcmp/lift/lift.pl lifts from bn_add.s, through nanofil.
# README.md has the results.
#
#   ./run.sh [WORKDIR]
#
# 1. The lifted IR with drive.ir: nanofil's interpreter against its
#    native code (tests/difftest.sh), the Rocq model against the
#    interpreter (rocq/scripts/agree.sh), the extracted validator
#    against ir:valid_module/1 (valid.sh), and the validator on the
#    checked module (gate.sh), each without and with -O.
# 2. harness.c linked with each build of the kernels: every build must
#    print what the interpreter returns for each run of drive.ir, and a
#    count past the end of the buffers must stop the checked builds.
# 3. Each build under zegarmistrz with both operands poisoned, as
#    upstream has the emulator and with
#    ../ct-memcmp/zegarmistrz-keep-taint.patch.
#
# Needs nix and GNU as. SWIPL, FILCC, MODEL, ZEGARMISTRZ and
# ZEGARMISTRZ_KEEP_TAINT name the tools; without them nix builds the
# pinned ones.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
memcmp=$repo/experiments/ct-memcmp
work=${1:-$(mktemp -d)}
mkdir -p "$work"
cd "$work"
work=$PWD

nixpkgs="(import (builtins.getFlake \"$repo\").inputs.nixpkgs { system = \"x86_64-linux\"; })"
build() { nix build --impure --no-link --print-out-paths --expr "$1" | head -1; }
SWIPL=${SWIPL:-$(build "$nixpkgs.swi-prolog")/bin/swipl}
FILCC=${FILCC:-$(nix build --no-link --print-out-paths "$repo#filcc-staging")/bin/clang}
MODEL=${MODEL:-$(nix build --no-link --print-out-paths "$repo#checks.x86_64-linux.nanofil-rocq.model")/bin/nanofil-model}
ZEGARMISTRZ=${ZEGARMISTRZ:-$(build "import $memcmp/zegarmistrz.nix { pkgs = $nixpkgs; }")/bin/zegarmistrz}
ZEGARMISTRZ_KEEP_TAINT=${ZEGARMISTRZ_KEEP_TAINT:-$(build "import $memcmp/zegarmistrz.nix { pkgs = $nixpkgs; keepTaint = true; }")/bin/zegarmistrz}
export SWIPL FILCC MODEL
nanofil=$repo/nanofil

fail() { echo "FAIL: $*" >&2; exit 1; }

echo "== the IR"
"$SWIPL" "$memcmp/lift/lift.pl" "$here/bn_add.s" >lifted.ir
cat lifted.ir "$here/drive.ir" >all-lifted.ir
# The runs of drive.ir, one a line: KERNEL SIZE N A0 ASTEP B0 BSTEP ret|trap VALUE.
runs() {
  (cd "$nanofil/src" && ../bin/nanofil "$@" outcomes "$work/all-lifted.ir" </dev/null) |
    sed -n 's/^outcome(drive_\([a-z]*\),\[\([0-9,]*\)\],[0-9]*,\([a-z]*\)(\([a-z0-9_]*\)))\.$/\1 \2 \3 \4/p' | tr , ' '
}
for opt in "" -O; do
  export NANOFIL_OPT=$opt
  "$nanofil/tests/difftest.sh" all-lifted.ir | tail -n 1
  "$nanofil/rocq/scripts/agree.sh" all-lifted.ir | tail -n 1
  NANOFIL_MUTANTS=0 "$nanofil/rocq/scripts/valid.sh" all-lifted.ir | tail -n 1
  "$nanofil/rocq/scripts/gate.sh" all-lifted.ir lifted.ir
  # shellcheck disable=SC2086
  runs $opt >runs$opt
done
unset NANOFIL_OPT
cmp runs runs-O || fail "the lifted IR gives a different outcome with -O"
[ -s runs ] || fail "drive.ir has no runs"

echo "== the builds"
compile_ir() { # compile_ir NAME OPT...: lifted.ir through nanofil
  local name=$1
  shift
  (cd "$nanofil/src" && ../bin/nanofil "$@" compile "$work/lifted.ir" </dev/null) >"$name.s"
  as -o "$name.o" "$name.s"
}
as -o zeg.o "$memcmp/zeg.s"
as -o bn-unchecked.o "$here/bn_add.s"
"$FILCC" -g -O2 -c -o bn-sarcasm.o "$here/bn_add.s"
compile_ir bn-lifted
compile_ir bn-lifted-O -O
# zunsafe_fast_call, which reaches zeg.s, needs -yolo-assembler.
"$FILCC" -g -O2 -yolo-assembler -c -o harness.o "$here/harness.c"
"$FILCC" -g -O2 -yolo-assembler -DUNCHECKED -c -o harness-unchecked.o "$here/harness.c"
builds="unchecked sarcasm lifted lifted-O"
for b in $builds; do
  h=harness.o
  [ "$b" = unchecked ] && h=harness-unchecked.o
  "$FILCC" -g -O2 -o "$b" "$h" "bn-$b.o" zeg.o
done

# The instructions of bn_add_words in a build, without alignment padding
# (objdump prints the two-byte nop as xchg %ax,%ax).
instructions() {
  objdump -d --no-show-raw-insn "$1" |
    awk '/^[0-9a-f]+ <(pizlonatedFI[A-Za-z0-9]*_)?bn_add_words>:/ { p = 1; next } p && /^$/ { exit } p && !/\tnop|\tint3|\tcs nop|\tdata16|\txchg +%ax,%ax/' |
    wc -l
}

# Each build on each run of drive.ir. Where the interpreter returns,
# every build prints that number. Where it traps, the count is past the
# end of the buffers: the checked builds panic, and the unchecked build
# writes past the end of r.
echo "== natively"
for b in $builds; do
  agree=0 stopped=0
  while read -r k size n a0 astep b0 bstep kind value; do
    set +e
    out=$("./$b" "$k" "$size" "$n" "$a0" "$astep" "$b0" "$bstep" 2>&1)
    status=$?
    set -e
    case $kind-$b in
      ret-*)
        [[ $status = 0 && $out = "$value" ]] || fail "$b $k $size $n $a0 $astep $b0 $bstep: $out, not $value"
        agree=$((agree + 1))
        ;;
      trap-unchecked) ;;
      trap-*)
        [[ $status != 0 && $out == *"filc safety error"* ]] || fail "$b $k went past the buffer: $out"
        stopped=$((stopped + 1))
        ;;
    esac
  done <runs
  printf '%-10s agrees with the interpreter on %d runs; a count past the buffers: %s; bn_add_words is %d instructions; ns/word: %s\n' \
    "$b" "$agree" "$([ "$b" = unchecked ] && echo "not checked" || echo "Fil-C panic ($stopped runs)")" \
    "$(instructions "$b")" "$("./$b" bench)"
done

# Every build of each kernel under the emulator, with both operands
# poisoned cannot-branch, cannot-index and cannot-var-time-op (0x4c):
# sums with no carry, a carry that ripples through every word, and
# carries in some words. Each run is made twice: under zegarmistrz as
# upstream has it, and under the build in which a tainted store keeps
# its taint.
echo "== under zegarmistrz (about 10 s a run)"
emulate() { # emulate EMULATOR BUILD KERNEL CASE ARGS...: one line in $1-$2-$3-$4.emu
  local out=$1-$2-$3-$4 status=0 emulator=$ZEGARMISTRZ
  [ "$1" = keep-taint ] && emulator=$ZEGARMISTRZ_KEEP_TAINT
  timeout 600 "$emulator" --no-core "./$2" "$3" "${@:5}" 0x4c >"$out.out" 2>"$out.err" || status=$?
  if [ $status = 0 ] && [ "$(cat "$out.out")" = "$("./$2" "$3" "${@:5}")" ]; then
    verdict=clean
  elif grep -q 'tainted (cannot-branch) value used in branch condition' "$out.err" &&
    grep -q "_words" "$out.err"; then
    verdict=cannot-branch
  else
    verdict="unexpected (exit $status)"
  fi
  printf '%-10s %-10s %-5s %-8s %s\n' "$1" "$2" "$3" "$4" "$verdict" >"$out.emu"
}
running=0
for e in upstream keep-taint; do
  for b in $builds; do
    for k in add sub leaky; do
      for c in "no-carry 4 4 3 5 7 11" "ripple 4 4 -1 0 1 0" "mixed 8 8 -3 1 1 1"; do
        # shellcheck disable=SC2086
        emulate "$e" "$b" "$k" $c &
        running=$((running + 1))
        if [ $running -ge "$(nproc)" ]; then wait -n; running=$((running - 1)); fi
      done
    done
  done
done
wait
cat ./*.emu
count() { cat "${@:2}" | grep -c " $1\$" || true; }
[ "$(count clean ./*-add-*.emu ./*-sub-*.emu)" = 48 ] ||
  fail "bn_add_words and bn_sub_words are not clean in every build under both emulators"
[ "$(count cannot-branch ./keep-taint-*-leaky-*.emu)" = 12 ] ||
  fail "leaky_add_words is not caught in every build when a tainted store keeps its taint"
# As with ../ct-memcmp's leaky_memcmp: upstream loses the taint of a
# value when it is stored to a stack slot that held a tainted value
# before, which the unoptimized lifted code does with the carry it
# branches on.
[ "$(count cannot-branch ./upstream-*-leaky-*.emu)" = 9 ] && [ "$(count clean ./upstream-lifted-leaky-*.emu)" = 3 ] ||
  fail "upstream zegarmistrz no longer misses leaky_add_words in exactly the unoptimized lifted build"
echo "ok: bn_add_words and bn_sub_words are clean in every build under both emulators; leaky_add_words is caught"
echo "    in every build when a tainted store keeps its taint, and upstream zegarmistrz misses it in the"
echo "    unoptimized lifted build"
