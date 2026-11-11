#!/usr/bin/env bash
# M2's gate (docs/lambda-anf.md): each program of Programs.v goes
# through CertiRocq's λANF (-O 1 --anf-variant 8) and its tap
# (nix/certirocq-anf-tap.patch), AnfLower.v (../anf-lower), and
# `nanofil-backend compile-allocated` (ValidFast.valid_fast, then
# Regs.v), is linked with the arena of nanofil/anf, and must print the
# bytes that the same program extracted to OCaml and built by ocamlopt
# prints: once with the default nursery, and once with a nursery of
# ANF_STRESS_NURSERY words (256) under FUGC_SCRIBBLE=1 FUGC_VERIFY=1,
# so that collections run in the middle of the program.
#
# Needs rocq with CertiRocq (nix/certirocq-anf.nix) on ROCQPATH,
# ocamlfind and zarith, and:
#   CERTIROCQ_SRC     CertiRocq's source (its tests/lib)
#   FILCC             Fil-C's clang (default /tmp/filcc/bin/clang)
#   NANOFIL_BACKEND   default rocq/backend/nanofil-backend, built if missing
#   ANF_PROGRAMS      the programs to run (default all)
#   ANF_WORK          the scratch directory (default a new one)
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
lower=$(cd "$here/.." && pwd)
nanofil=$(cd "$lower/../.." && pwd)
filcc=${FILCC:-/tmp/filcc/bin/clang}
backend=${NANOFIL_BACKEND:-$nanofil/rocq/backend/nanofil-backend}
stress=${ANF_STRESS_NURSERY:-256}
: "${CERTIROCQ_SRC:?the CertiRocq source, for its tests/lib}"
programs=${ANF_PROGRAMS:-demo1 demo2 list_sum vs_easy vs_hard binom color clos rec_clos rec_clos2 sha_fast order asm}
work=${ANF_WORK:-$(mktemp -d)}
mkdir -p "$work"
echo "work: $work"
stamp() { date -u +%H:%M:%S; }

[[ -x $backend ]] || make -C "$nanofil/rocq/backend" -j"${NIX_BUILD_CORES:-4}" >"$work/backend.log"
make -C "$lower" >"$work/anf-lower.log"

echo "$(stamp) the programs and their λANF"
mkdir -p "$work/lib" "$work/t"
cp "$CERTIROCQ_SRC"/tests/lib/{vs,Binom,Color,sha256}.v "$work/lib/"
chmod u+w "$work/lib"/*.v
(cd "$work/lib" && for f in Binom Color vs sha256; do
   rocq compile -w -all -R . CertiRocq.Tests.lib "$f.v"
 done)
cp "$here"/{Show,Programs,Tap,Ref}.v "$work/t/"
flags=(-w -all -R "$work/lib" CertiRocq.Tests.lib -R "$nanofil/rocq/theories" Nanofil
       -R "$nanofil/rocq/backend" Backend -R . AnfTests)
(cd "$work/t" && rocq compile "${flags[@]}" Show.v && rocq compile "${flags[@]}" Programs.v)
t0=$SECONDS
(cd "$work/t" && rocq compile "${flags[@]}" Tap.v)
echo "$(stamp) tapped in $((SECONDS - t0)) s"

echo "$(stamp) the OCaml reference"
# One extraction per program (Ref.v), so that each reference computes
# its own program only: OCaml evaluates a module's values when it
# loads. The .mli extraction writes for Color's FMapPositive is not
# OCaml (an unbound 'A); the .ml alone is.
(cd "$work/t" && rocq compile "${flags[@]}" Ref.v && rm -f ref_*.mli &&
   for p in $programs; do
     printf 'let rec go = function\n  | Ref_%s.Nil -> ()\n  | Ref_%s.Cons (b, r) -> print_char (Char.chr (Obj.magic b : int)); go r\nlet () = go Ref_%s.%s_out\n' \
       "$p" "$p" "$p" "$p" >"main_$p.ml"
     ocamlfind ocamlopt -w -a -O3 "ref_$p.ml" "main_$p.ml" -o "ref_$p" 2>/dev/null ||
       ocamlfind ocamlopt -w -a "ref_$p.ml" "main_$p.ml" -o "ref_$p"
   done)

echo "$(stamp) the runtime"
"$filcc" -O2 -c -I"$nanofil/anf" -o "$work/anf_arena.o" "$nanofil/anf/anf_arena.c"
"$filcc" -O2 -c -o "$work/rt.o" "$lower/anf_lower_rt.c"
"$filcc" -O2 -c -o "$work/driver.o" "$lower/driver.c"

# Direct-style code recurses as deep as the lists it builds (List.app,
# List.repeat, String.append over 100k characters), in OCaml as in the
# arena: both run with the same stack, and once more each with the
# default 8 MB, to show which programs need more.
big_stack=${ANF_STACK_KB:-1048576}
# The best of three wall times, in ms, of the command.
best_ms() {
  local best=
  for _ in 1 2 3; do
    local t0 t1
    t0=$(date +%s%N); "$@" >/dev/null 2>&1; t1=$(date +%s%N)
    local ms=$(((t1 - t0) / 1000000))
    [[ -z $best || $ms -lt $best ]] && best=$ms
  done
  echo "$best"
}
bad=0
printf '%-10s %6s %6s %6s %6s %9s %9s %8s %8s %8s %8s %s\n' program fns irfns blocks fids \
  asm-lines out-bytes gcs stress-gcs arena-ms ocaml-ms verdict
for p in $programs; do
  ir=$(ls "$work"/t/*."${p}_out.ir" 2>/dev/null | head -1)
  if [[ -z $ir ]]; then echo "$p: no λANF"; bad=$((bad + 1)); continue; fi
  if ! "$lower/anf-lower" "$ir" >"$work/$p.nir" 2>"$work/$p.lower.err"; then
    echo "$p: anf-lower refuses: $(cat "$work/$p.lower.err")"; bad=$((bad + 1)); continue
  fi
  if ! "$backend" compile-allocated "$work/$p.nir" >"$work/$p.s" 2>"$work/$p.backend.err"; then
    echo "$p: nanofil-backend refuses: $(cat "$work/$p.backend.err")"; bad=$((bad + 1)); continue
  fi
  as -o "$work/$p.o" "$work/$p.s"
  "$filcc" -o "$work/$p" "$work/driver.o" "$work/rt.o" "$work/anf_arena.o" "$work/$p.o"
  (ulimit -s "$big_stack"; "$work/t/ref_$p" >"$work/$p.ref")
  verdict=same
  (ulimit -s "$big_stack"; "$work/$p" >"$work/$p.out" 2>"$work/$p.err") || verdict="EXIT $?"
  cmp -s "$work/$p.out" "$work/$p.ref" || verdict="DIFFER"
  (ulimit -s "$big_stack"
   ANF_NURSERY=$stress FUGC_SCRIBBLE=1 FUGC_VERIFY=1 "$work/$p" >"$work/$p.stress.out" 2>"$work/$p.stress.err") ||
    verdict="$verdict, stress EXIT $?"
  cmp -s "$work/$p.stress.out" "$work/$p.ref" || verdict="$verdict, stress DIFFER"
  [[ $verdict == same ]] || bad=$((bad + 1))
  small=ok
  (ulimit -s 8192; "$work/$p" >"$work/$p.8mb.out" 2>/dev/null) || small="EXIT-$?"
  [[ $small != ok ]] || cmp -s "$work/$p.8mb.out" "$work/$p.ref" || small=DIFFER
  osmall=ok
  (ulimit -s 8192; "$work/t/ref_$p" >/dev/null 2>&1) || osmall="EXIT-$?"
  verdict="$verdict (8MB: arena $small, ocaml $osmall)"
  arena_ms=$(ulimit -s "$big_stack"; best_ms "$work/$p")
  ocaml_ms=$(ulimit -s "$big_stack"; best_ms "$work/t/ref_$p")
  printf '%-10s %6s %6s %6s %6s %9s %9s %8s %8s %8s %8s %s\n' "$p" \
    "$(sed -n 's/^anf-lower: \([0-9]*\) functions.*/\1/p' "$work/$p.lower.err")" \
    "$(grep -c '^func(' "$work/$p.nir")" \
    "$(sed -n 's/.* \([0-9]*\) as blocks.*/\1/p' "$work/$p.lower.err")" \
    "$(sed -n 's/.* \([0-9]*\) with fids.*/\1/p' "$work/$p.lower.err")" \
    "$(wc -l <"$work/$p.s")" "$(wc -c <"$work/$p.ref")" \
    "$(sed -n 's/^anf: \([0-9]*\) minor.*/\1/p' "$work/$p.err")" \
    "$(sed -n 's/^anf: \([0-9]*\) minor.*/\1/p' "$work/$p.stress.err")" "$arena_ms" "$ocaml_ms" "$verdict"
done
echo "$(stamp) $bad of $(echo $programs | wc -w) programs differ or fail"
exit $((bad > 0))
