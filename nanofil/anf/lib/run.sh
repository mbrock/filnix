#!/usr/bin/env bash
# libnanofil's gate (docs/lambda-anf.md, M4): the Gallina backend as
# ../backend/run.sh builds it (CertiRocq's λANF of ../backend/Drive.v's
# run, AnfLower.v, `nanofil-backend compile-allocated`), linked with the
# arena, the primitives and libnanofil.c into libnanofil.so, which
# exports nanofil.h's functions and nothing else. Then test_lib, one
# process over the library's one arena, compiles every IR fixture with
# compile, compile-promoted and compile-allocated, ANF_ROUNDS times (3)
# in alternating orders; every compile must exit as the OCaml build of
# the backend exits, say what it says on stderr and, when it succeeds,
# print what it prints. The same again with
# a nursery of ANF_STRESS_NURSERY words (4096) under FUGC_SCRIBBLE=1
# FUGC_VERIFY=1. Then, for each FILE.ir in ANF_BENCH, the time of the
# first compile in a process and the best of ten after it.
#
# Needs what ../backend/run.sh needs (nix-shell ../lower/shell.nix):
#   FILCC             Fil-C's clang (default /tmp/filcc/bin/clang)
#   NANOFIL_BACKEND   default rocq/backend/nanofil-backend, built if missing
#   ANF_FIXTURES      the fixtures (default those of rocq/backend's gates)
#   ANF_BENCH         IR files to time (default none)
#   ANF_WORK          the scratch directory (default a new one); a
#                     backend.s already in it is used as it is
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
anf=$(cd "$here/.." && pwd)
nanofil=$(cd "$anf/.." && pwd)
filcc=${FILCC:-/tmp/filcc/bin/clang}
backend=${NANOFIL_BACKEND:-$nanofil/rocq/backend/nanofil-backend}
stress=${ANF_STRESS_NURSERY:-4096}
rounds=${ANF_ROUNDS:-3}
work=${ANF_WORK:-$(mktemp -d)}
mkdir -p "$work/t"
echo "work: $work"
stamp() { date -u +%H:%M:%S; }

[[ -x $backend ]] || make -C "$nanofil/rocq/backend" -j"${NIX_BUILD_CORES:-4}" >"$work/backend.log"
if [[ ! -s $work/backend.s ]]; then
  make -C "$nanofil/rocq/backend" -j"${NIX_BUILD_CORES:-4}" Compile.vo Layout.vo Asm.vo IrText.vo \
    ../theories/core/Maps.vo >>"$work/backend.log"
  make -C "$anf/lower" >"$work/anf-lower.log"
  echo "$(stamp) the backend's λANF"
  cp "$anf/lower/Prims.v" "$anf/backend"/{Drive,Tap}.v "$work/t/"
  flags=(-w -all -R "$nanofil/rocq/theories" Nanofil -R "$nanofil/rocq/backend" Backend -R . AnfBackend)
  t0=$SECONDS
  (cd "$work/t" && rocq compile "${flags[@]}" Prims.v && rocq compile "${flags[@]}" Drive.v &&
     rocq compile "${flags[@]}" Tap.v)
  echo "$(stamp) tapped in $((SECONDS - t0)) s"
  t0=$SECONDS
  "$anf/lower/anf-lower" "$work/t/AnfBackend.Drive.run.ir" >"$work/backend.nir" 2>"$work/lower.err"
  echo "$(stamp) lowered in $((SECONDS - t0)) s: $(cat "$work/lower.err")"
  t0=$SECONDS
  "$backend" compile-allocated "$work/backend.nir" >"$work/backend.s.tmp"
  mv "$work/backend.s.tmp" "$work/backend.s"
  echo "$(stamp) compiled in $((SECONDS - t0)) s ($(wc -l <"$work/backend.s") lines of assembly)"
fi

t0=$SECONDS
as -o "$work/backend.o" "$work/backend.s"
for c in "$anf/anf_arena.c" "$anf/lower/anf_lower_rt.c" "$anf/lower/anf_prims.c" "$here/libnanofil.c"; do
  "$filcc" -O2 -fPIC -c -I"$anf" -o "$work/$(basename "$c" .c).o" "$c"
done
# Only nanofil_* is exported. Fil-C's linker reads the names of a
# version script as C names and exports their getters (pizlonated_f).
printf '{ global: nanofil_*; local: *; };\n' >"$work/libnanofil.map"
"$filcc" -shared -Wl,--version-script="$work/libnanofil.map" -o "$work/libnanofil.so" \
  "$work"/{libnanofil,anf_arena,anf_lower_rt,anf_prims,backend}.o -lpthread
"$filcc" -O2 -I"$here" -o "$work/test_lib" "$here/test_lib.c" -L"$work" -lnanofil -Wl,-rpath,"$work"
echo "$(stamp) libnanofil.so linked in $((SECONDS - t0)) s ($(stat -c %s "$work/libnanofil.so") bytes)"
echo "exports: $(nm -D --defined-only "$work/libnanofil.so" | awk '{print $3}' | tr '\n' ' ')"

if [[ -n ${ANF_FIXTURES:-} ]]; then
  fixtures=($ANF_FIXTURES)
else
  shopt -s nullglob
  fixtures=("$nanofil"/tests/filc/*.ir "$nanofil"/rocq/backend/tests/{edge,pizlonate,compile,promote,regs}/*.ir)
fi
cmds=(compile compile-promoted compile-allocated)
mkdir -p "$work/ref" "$work/lib" "$work/stress"
for i in "${!fixtures[@]}"; do
  for c in 0 1 2; do
    status=0
    "$backend" "${cmds[$c]}" "${fixtures[$i]}" >"$work/ref/$i.$c.out" 2>"$work/ref/$i.$c.err" || status=$?
    echo "$status" >"$work/ref/$i.$c.status"
  done
done

# The library runs on its caller's stack, and its direct-style recursion
# over a module's lists is as deep as they are long; the fixtures need
# far less than the usual 8 MB, so the gate runs on the stack it is
# given unless ANF_STACK_KB says otherwise.
[[ -z ${ANF_STACK_KB:-} ]] || ulimit -s "$ANF_STACK_KB"
bad=0
for mode in lib stress; do
  t0=$SECONDS
  status=0
  if [[ $mode == lib ]]; then
    "$work/test_lib" "$work/lib" "$rounds" "${fixtures[@]}" || status=$?
  else
    ANF_NURSERY=$stress FUGC_SCRIBBLE=1 FUGC_VERIFY=1 \
      "$work/test_lib" "$work/stress" "$rounds" "${fixtures[@]}" || status=$?
  fi
  [[ $status == 0 ]] || { echo "DIFFER $mode: test_lib exited $status"; bad=$((bad + 1)); }
  for i in "${!fixtures[@]}"; do
    for c in 0 1 2; do
      # When a module is refused, nanofil-backend has already printed the
      # lines of the functions before the one it refuses; the library
      # gives only the reason.
      parts=(err status)
      [[ $(cat "$work/ref/$i.$c.status") != 0 ]] || parts+=(out)
      for part in "${parts[@]}"; do
        if ! cmp -s "$work/$mode/$i.$c.$part" "$work/ref/$i.$c.$part"; then
          echo "DIFFER $mode ${cmds[$c]} ${fixtures[$i]#"$nanofil"/}: $part"
          bad=$((bad + 1))
        fi
      done
    done
  done
  echo "$(stamp) $mode: ${#fixtures[@]} fixtures x 3 commands x $rounds rounds in one process, $((SECONDS - t0)) s"
done
echo "$(stamp) $bad differences"

for f in ${ANF_BENCH:-}; do
  for c in 0 2; do
    "$work/test_lib" --time 11 "$f" "$c"
  done
done
exit $((bad > 0))
