#!/usr/bin/env bash
# OpenSSL's CRYPTO_memcmp and an early-exit control, three ways: as
# plain assembly called unchecked, as the same assembly through SaRCAsm,
# and as nanofil IR through nanofil. The IR is the hand translation in
# memcmp.ir and, separately, what lift/lift.pl makes of memcmp.s.
# README.md has the results.
#
#   ./run.sh [WORKDIR]
#
# 1. Each IR with drive.ir: nanofil's interpreter against its native
#    code (tests/difftest.sh), the Rocq model against the interpreter
#    (rocq/scripts/agree.sh), the extracted validator against
#    ir:valid_module/1 (valid.sh), and the validator on the checked
#    module (gate.sh), each without and with -O. The lifted IR must give
#    the hand translation's outcome on every run of drive.ir.
# 2. harness.c linked with each build of the kernels: the same table of
#    results, and a length past the end of the buffers.
# 3. Each build under zegarmistrz with both buffers poisoned, as upstream
#    has the emulator and with zegarmistrz-keep-taint.patch.
#
# Needs nix and GNU as. SWIPL, FILCC, MODEL, ZEGARMISTRZ and
# ZEGARMISTRZ_KEEP_TAINT name the tools; without them nix builds the
# pinned ones.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
work=${1:-$(mktemp -d)}
mkdir -p "$work"
cd "$work"
work=$PWD

nixpkgs="(import (builtins.getFlake \"$repo\").inputs.nixpkgs { system = \"x86_64-linux\"; })"
build() { nix build --impure --no-link --print-out-paths --expr "$1" | head -1; }
SWIPL=${SWIPL:-$(build "$nixpkgs.swi-prolog")/bin/swipl}
FILCC=${FILCC:-$(nix build --no-link --print-out-paths "$repo#filcc-staging")/bin/clang}
MODEL=${MODEL:-$(nix build --no-link --print-out-paths "$repo#checks.x86_64-linux.nanofil-rocq.model")/bin/nanofil-model}
ZEGARMISTRZ=${ZEGARMISTRZ:-$(build "import $here/zegarmistrz.nix { pkgs = $nixpkgs; }")/bin/zegarmistrz}
ZEGARMISTRZ_KEEP_TAINT=${ZEGARMISTRZ_KEEP_TAINT:-$(build "import $here/zegarmistrz.nix { pkgs = $nixpkgs; keepTaint = true; }")/bin/zegarmistrz}
export SWIPL FILCC MODEL
nanofil=$repo/nanofil

fail() { echo "FAIL: $*" >&2; exit 1; }

echo "== the IR"
cp "$here/memcmp.ir" hand.ir
"$SWIPL" "$here/lift/lift.pl" "$here/memcmp.s" >lifted.ir
outcomes() { # outcomes IR OPT...: the result of each run of drive.ir
  (cd "$nanofil/src" && ../bin/nanofil "${@:2}" outcomes "$work/$1" </dev/null) | grep '^outcome('
}
for ir in hand lifted; do
  cat $ir.ir "$here/drive.ir" >all-$ir.ir
  for opt in "" -O; do
    export NANOFIL_OPT=$opt
    "$nanofil/tests/difftest.sh" all-$ir.ir | tail -n 1
    "$nanofil/rocq/scripts/agree.sh" all-$ir.ir | tail -n 1
    NANOFIL_MUTANTS=0 "$nanofil/rocq/scripts/valid.sh" all-$ir.ir | tail -n 1
    "$nanofil/rocq/scripts/gate.sh" all-$ir.ir $ir.ir
    # shellcheck disable=SC2086
    outcomes all-$ir.ir $opt >$ir$opt.outcomes
  done
  unset NANOFIL_OPT
done
for opt in "" -O; do
  cmp hand.outcomes lifted$opt.outcomes || fail "the lifted IR${opt:+ with $opt} and the hand translation differ on a run"
done
echo "ok: the lifted IR gives the hand translation's outcome on all $(wc -l <hand.outcomes) runs"

echo "== the builds"
compile_ir() { # compile_ir NAME IR OPT...: an IR file through nanofil
  local name=$1 ir=$2
  shift 2
  (cd "$nanofil/src" && ../bin/nanofil "$@" compile "$work/$ir" </dev/null) >"$name.s"
  as -o "$name.o" "$name.s"
}
as -o zeg.o "$here/zeg.s"
as -o memcmp-unchecked.o "$here/memcmp.s"
"$FILCC" -g -O2 -c -o memcmp-sarcasm.o "$here/memcmp.s"
compile_ir memcmp-nanofil hand.ir
compile_ir memcmp-nanofil-O hand.ir -O
compile_ir memcmp-lifted lifted.ir
compile_ir memcmp-lifted-O lifted.ir -O
# zunsafe_fast_call, which reaches zeg.s, needs -yolo-assembler.
"$FILCC" -g -O2 -yolo-assembler -c -o harness.o "$here/harness.c"
"$FILCC" -g -O2 -yolo-assembler -DUNCHECKED -c -o harness-unchecked.o "$here/harness.c"
builds="unchecked sarcasm nanofil nanofil-O lifted lifted-O"
for b in $builds; do
  h=harness.o
  [ "$b" = unchecked ] && h=harness-unchecked.o
  "$FILCC" -g -O2 -o "$b" "$h" "memcmp-$b.o" zeg.o
done

# The instructions of ct_memcmp in a build, without alignment padding
# (objdump prints the two-byte nop as xchg %ax,%ax).
instructions() {
  objdump -d --no-show-raw-insn "$1" |
    awk '/^[0-9a-f]+ <(pizlonatedFI[A-Za-z0-9]*_)?ct_memcmp>:/ { p = 1; next } p && /^$/ { exit } p && !/\tnop|\tint3|\tcs nop|\tdata16|\txchg +%ax,%ax/' |
    wc -l
}

echo "== natively"
for b in $builds; do
  "./$b" table >"$b.table"
  cmp -s unchecked.table "$b.table" || fail "$b prints a different table"
  # A length of 4096 on 16-byte buffers.
  set +e
  over=$("./$b" ct 16 4096 -1 2>&1)
  status=$?
  set -e
  case $b in
    unchecked) [ $status = 0 ] || fail "unchecked did not read past the buffer" ;;
    *) [[ $status != 0 && $over == *"filc safety error"* ]] || fail "$b read past the buffer: $over" ;;
  esac
  printf '%-10s table agrees (%d cases); overlong length: %s; ct_memcmp is %d instructions; ns/byte: %s\n' \
    "$b" "$(wc -l <"$b.table")" "$([ $status = 0 ] && echo "returns $over" || echo "Fil-C panic")" \
    "$(instructions "$b")" "$("./$b" bench)"
done

# Every build of each kernel under the emulator, with both buffers
# poisoned cannot-branch, cannot-index and cannot-var-time-op (0x4c):
# the 16-byte path, the byte loop with a difference, and equal buffers.
# Each run is made twice: under zegarmistrz as upstream has it, and under
# the build in which a tainted store keeps its taint
# (zegarmistrz-keep-taint.patch).
echo "== under zegarmistrz (about 10 s a run)"
emulate() { # emulate EMULATOR BUILD KERNEL SIZE LEN AT: one line in $1-$2-$3-$4-$6.emu
  local out=$1-$2-$3-$4-$6 status=0 emulator=$ZEGARMISTRZ
  [ "$1" = keep-taint ] && emulator=$ZEGARMISTRZ_KEEP_TAINT
  timeout 600 "$emulator" --no-core "./$2" "$3" "$4" "$5" "$6" 0x4c >"$out.out" 2>"$out.err" || status=$?
  if [ $status = 0 ] && [ "$(cat "$out.out")" = "$("./$2" "$3" "$4" "$5" "$6")" ]; then
    verdict=clean
  elif grep -q 'tainted (cannot-branch) value used in branch condition' "$out.err" &&
    grep -q "_memcmp" "$out.err"; then
    verdict=cannot-branch
  else
    verdict="unexpected (exit $status)"
  fi
  printf '%-10s %-10s %-5s size %-3s len %-3s differ at %-3s %s\n' "$1" "$2" "$3" "$4" "$5" "$6" "$verdict" >"$out.emu"
}
running=0
for e in upstream keep-taint; do
  for b in $builds; do
    for k in ct leaky; do
      for c in "16 16 9" "32 32 20" "32 32 -1"; do
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
[ "$(count clean ./*-ct-*.emu)" = 36 ] || fail "ct_memcmp is not clean in every build under both emulators"
[ "$(count cannot-branch ./keep-taint-*-leaky-*.emu)" = 18 ] ||
  fail "leaky_memcmp is not caught in every build when a tainted store keeps its taint"
# Upstream loses the taint of a value when it is stored to a stack slot
# that held a tainted value before, which the unoptimized lifted code
# does with the condition of the early exit.
[ "$(count cannot-branch ./upstream-*-leaky-*.emu)" = 15 ] && [ "$(count clean ./upstream-lifted-leaky-*.emu)" = 3 ] ||
  fail "upstream zegarmistrz no longer misses leaky_memcmp in exactly the unoptimized lifted build"
echo "ok: ct_memcmp is clean in every build under both emulators; leaky_memcmp is caught in every build when a"
echo "    tainted store keeps its taint, and upstream zegarmistrz misses it in the unoptimized lifted build"
