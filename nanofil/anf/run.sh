#!/usr/bin/env bash
# Build and verify nanofil/anf/anf_arena.c as a verified-clean Fil-C module
# through both the extracted Gallina backend (Compile.compile_allocated) and
# Prolog nanofil (-O), then run the M1 stress/OOM gate and RSS probe under
# FUGC_SCRIBBLE=1 FUGC_VERIFY=1.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
nanofil_root=$(cd "$here/.." && pwd)
nanofil="$nanofil_root/bin/nanofil"
filcc=${FILCC:-/tmp/filcc/bin/clang}
swipl=${SWIPL:-/tmp/swipl/bin/swipl}
backend=${NANOFIL_BACKEND:-/tmp/nanofil-backend/bin/nanofil-backend}
export SWIPL="$swipl" FILCC="$filcc"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

echo "=== 1. Lower anf_arena.c via nanofil cc-ir and check Gallina backend parity ==="
(cd "$nanofil_root/src" && "$nanofil" cc-ir "$here/anf_arena.c" </dev/null) >"$work/anf_arena.ir"

if [[ -x "$backend" ]]; then
  for mode in compile compile-promoted; do
    (cd "$nanofil_root/src" && "$nanofil" "$mode" "$work/anf_arena.ir" </dev/null) >"$work/pl-$mode.s"
    "$backend" "$mode" "$work/anf_arena.ir" >"$work/nb-$mode.s"
    cmp -s "$work/pl-$mode.s" "$work/nb-$mode.s" || {
      echo "MISMATCH between Prolog nanofil and nanofil-backend on $mode" >&2
      exit 1
    }
    echo "  ok: $mode byte-identical ($(wc -l <"$work/nb-$mode.s") asm lines)"
  done
  (cd "$nanofil_root/src" && "$nanofil" encode-input "$work/anf_arena.ir" "$work/anf_arena.nfb" </dev/null)
  "$backend" compile-nfb "$work/anf_arena.nfb" >"$work/nb-nfb.s"
  cmp -s "$work/nb-compile.s" "$work/nb-nfb.s" || {
    echo "MISMATCH on compile-nfb" >&2
    exit 1
  }
  echo "  ok: NFB round-trip compile-nfb byte-identical ($(wc -c <"$work/anf_arena.nfb") bytes)"

  "$backend" compile-allocated "$work/anf_arena.ir" >"$work/anf_arena_allocated.s"
  echo "  ok: nanofil-backend compile-allocated ($(wc -l <"$work/anf_arena_allocated.s") asm lines, ValidFast.valid_fast + Regs.valid_alloc)"
  as -o "$work/anf_arena_nb.o" "$work/anf_arena_allocated.s"
  "$filcc" -O1 -I"$here" -o "$work/test_arena_nb" "$here/test_arena.c" "$work/anf_arena_nb.o"
  echo "=== 2. Run M1 stress + OOM suite (Gallina compile-allocated, FUGC_SCRIBBLE=1 FUGC_VERIFY=1) ==="
  FUGC_SCRIBBLE=1 FUGC_VERIFY=1 "$work/test_arena_nb"
fi

echo "=== 3. Compile anf_arena.c via Prolog nanofil -O cc and run M1 stress + OOM suite ==="
(cd "$nanofil_root/src" && "$nanofil" -O cc "$here/anf_arena.c" </dev/null) >"$work/anf_arena_opt.s"
echo "  ok: nanofil -O cc ($(wc -l <"$work/anf_arena_opt.s") asm lines)"
as -o "$work/anf_arena_opt.o" "$work/anf_arena_opt.s"
"$filcc" -O1 -I"$here" -o "$work/test_arena_opt" "$here/test_arena.c" "$work/anf_arena_opt.o"
FUGC_SCRIBBLE=1 FUGC_VERIFY=1 "$work/test_arena_opt"

if [[ "${RUN_MMAP_PROBE:-1}" == "1" ]]; then
  echo "=== 4. Run zsys_mmap(MAP_NORESERVE) & zsys_madvise(MADV_DONTNEED) RSS probe ==="
  obj="$work/anf_arena_opt.o"
  [[ -f "$work/anf_arena_nb.o" ]] && obj="$work/anf_arena_nb.o"
  "$filcc" -O1 -I"$here" -o "$work/probe_mmap" "$here/probe_mmap.c" "$obj"
  "$work/probe_mmap"
  echo "--- Under FUGC_SCRIBBLE=1 FUGC_VERIFY=1 (lifecycle only) ---"
  FUGC_SCRIBBLE=1 FUGC_VERIFY=1 "$work/probe_mmap"
fi
