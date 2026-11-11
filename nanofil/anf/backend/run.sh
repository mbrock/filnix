#!/usr/bin/env bash
# M3's gate (docs/lambda-anf.md): the Gallina backend (rocq/backend)
# through CertiRocq's λANF (-O 1 --anf-variant 8) and its tap
# (nix/certirocq-anf-tap.patch), with the constants of ../lower/Prims.v
# and Tap.v left as primitives, AnfLower.v (../lower/anf-lower) and
# `nanofil-backend compile-allocated`, linked with the arena of
# nanofil/anf, the primitives (../lower/anf_prims.c) and driver.c. On
# each fixture, for each of compile, compile-promoted and
# compile-allocated, it must print what the OCaml build of the same
# backend (rocq/backend/nanofil-backend) prints, say the same on stderr
# and end with its status: once with the default nursery, and once with a nursery of
# ANF_STRESS_NURSERY words (4096). Then, for each FILE.ir in
# ANF_BENCH, the best of three wall times of both on compile and
# compile-allocated.
#
# Needs what ../lower/tests/run.sh needs (nix-shell ../lower/shell.nix),
# and:
#   FILCC             Fil-C's clang (default /tmp/filcc/bin/clang)
#   NANOFIL_BACKEND   default rocq/backend/nanofil-backend, built if missing
#   ANF_FIXTURES      the fixtures (default those of rocq/backend's gates)
#   ANF_BENCH         IR files to time, such as rx.ir (default none)
#   ANF_WORK          the scratch directory (default a new one)
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
anf=$(cd "$here/.." && pwd)
nanofil=$(cd "$anf/.." && pwd)
filcc=${FILCC:-/tmp/filcc/bin/clang}
backend=${NANOFIL_BACKEND:-$nanofil/rocq/backend/nanofil-backend}
stress=${ANF_STRESS_NURSERY:-4096}
work=${ANF_WORK:-$(mktemp -d)}
mkdir -p "$work/t"
echo "work: $work"
stamp() { date -u +%H:%M:%S; }

[[ -x $backend ]] || make -C "$nanofil/rocq/backend" -j"${NIX_BUILD_CORES:-4}" >"$work/backend.log"
make -C "$nanofil/rocq/backend" -j"${NIX_BUILD_CORES:-4}" Compile.vo Layout.vo Asm.vo IrText.vo Encode.vo Elf.vo \
  ../theories/core/Maps.vo >>"$work/backend.log"
make -C "$anf/lower" >"$work/anf-lower.log"

echo "$(stamp) the backend's λANF"
cp "$anf/lower/Prims.v" "$anf/rx/Rx.v" "$here"/{Drive,Tap}.v "$work/t/"
flags=(-w -all -R "$nanofil/rocq/theories" Nanofil -R "$nanofil/rocq/backend" Backend -R . AnfBackend)
t0=$SECONDS
(cd "$work/t" && rocq compile "${flags[@]}" Prims.v && rocq compile "${flags[@]}" Rx.v &&
   rocq compile "${flags[@]}" Drive.v && rocq compile "${flags[@]}" Tap.v)
echo "$(stamp) tapped in $((SECONDS - t0)) s"

t0=$SECONDS
"$anf/lower/anf-lower" "$work/t/AnfBackend.Drive.run.ir" >"$work/backend.nir" 2>"$work/lower.err"
echo "$(stamp) lowered in $((SECONDS - t0)) s: $(cat "$work/lower.err")"
t0=$SECONDS
"$backend" compile-allocated "$work/backend.nir" >"$work/backend.s"
as -o "$work/backend.o" "$work/backend.s"
"$filcc" -O2 -c -I"$anf" -o "$work/anf_arena.o" "$anf/anf_arena.c"
"$filcc" -O2 -c -o "$work/rt.o" "$anf/lower/anf_lower_rt.c"
"$filcc" -O2 -c -o "$work/prims.o" "$anf/lower/anf_prims.c"
"$filcc" -O2 -c -o "$work/driver.o" "$here/driver.c"
"$filcc" -o "$work/anf-backend" "$work/driver.o" "$work/rt.o" "$work/prims.o" "$work/anf_arena.o" "$work/backend.o"
echo "$(stamp) compiled and linked in $((SECONDS - t0)) s ($(wc -l <"$work/backend.s") lines of assembly)"

# Direct-style recursion over a module's lists is as deep as they are
# long; both builds run with the same stack.
ulimit -s "${ANF_STACK_KB:-1048576}"

if [[ -n ${ANF_FIXTURES:-} ]]; then
  fixtures=($ANF_FIXTURES)
else
  shopt -s nullglob
  fixtures=("$nanofil"/tests/filc/*.ir "$nanofil"/rocq/backend/tests/{edge,pizlonate,compile,promote,regs}/*.ir)
fi
bad=0 runs=0
for f in "${fixtures[@]}"; do
  for cmd in compile compile-promoted compile-allocated; do
    runs=$((runs + 1))
    ref_status=0 status=0 stress_status=0
    "$backend" "$cmd" "$f" >"$work/ref.out" 2>"$work/ref.err" || ref_status=$?
    "$work/anf-backend" "$cmd" "$f" >"$work/anf.out" 2>"$work/anf.err" || status=$?
    ANF_NURSERY=$stress "$work/anf-backend" "$cmd" "$f" >"$work/stress.out" 2>/dev/null || stress_status=$?
    why=
    [[ $status == "$ref_status" ]] || why="$why status $status, not $ref_status;"
    cmp -s "$work/anf.out" "$work/ref.out" || why="$why output differs;"
    cmp -s "$work/anf.err" "$work/ref.err" || why="$why stderr differs;"
    [[ $stress_status == "$ref_status" ]] || why="$why stress status $stress_status;"
    cmp -s "$work/stress.out" "$work/ref.out" || why="$why stress output differs;"
    if [[ -n $why ]]; then
      bad=$((bad + 1))
      echo "DIFFER $cmd ${f#"$nanofil"/}:$why $(head -c 300 "$work/anf.err")"
    fi
  done
done
echo "$(stamp) $bad of $runs runs ($((runs / 3)) fixtures) differ"

# The best of three wall times, in ms, of the command.
best_ms() {
  local best=
  for _ in 1 2 3; do
    local t0 t1
    t0=$(date +%s%N); "$@" >/dev/null 2>&1 || true; t1=$(date +%s%N)
    local ms=$(((t1 - t0) / 1000000))
    [[ -z $best || $ms -lt $best ]] && best=$ms
  done
  echo "$best"
}
for f in ${ANF_BENCH:-}; do
  for cmd in compile compile-allocated; do
    same=same
    "$backend" "$cmd" "$f" >"$work/ref.out" 2>/dev/null || true
    "$work/anf-backend" "$cmd" "$f" >"$work/anf.out" 2>/dev/null || same="EXIT $?"
    cmp -s "$work/anf.out" "$work/ref.out" || same="$same, DIFFER"
    printf '%-24s %-18s arena %6s ms  ocamlopt %6s ms  %s\n' "$(basename "$f")" "$cmd" \
      "$(best_ms "$work/anf-backend" "$cmd" "$f")" "$(best_ms "$backend" "$cmd" "$f")" "$same"
  done
done
exit $((bad > 0))
