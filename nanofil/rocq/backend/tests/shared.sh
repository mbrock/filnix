#!/usr/bin/env bash
# The shared-object writer (Elf.v): for each tests/filc fixture with a
# C driver and a .expected, `nanofil-backend shared...` writes the
# shared object of the module with compile and with compile-allocated,
# filcc links the driver against it, and each run of the driver must
# print its line of .expected, as tests/regs.sh runs it against the
# object GNU as makes, under FUGC_SCRIBBLE=1 FUGC_VERIFY=1. A module the
# backend does not compile is skipped; one it compiles but Elf.v does
# not link fails.
#
#   FILCC=.../clang shared.sh FILE.ir...
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
backend=${BACKEND:-$here/../nanofil-backend}
filcc=${FILCC:?set FILCC to a filcc clang}
as=${AS:-as}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

same=0 skipped=0 status=0
for f in "$@"; do
  stem=${f%.ir}
  [[ -f $stem.c && -f $stem.expected ]] || continue
  for c in compile compile-allocated; do
    if ! "$backend" "$c" "$f" >/dev/null 2>&1; then
      skipped=$((skipped + 1)); continue
    fi
    if ! "$backend" "${c/compile/shared}" "$f" "$work/m.so" 2>"$work/err"; then
      echo "NOT LINKED $c $f: $(head -1 "$work/err")"; status=1; continue
    fi
    extra=()
    if [[ -f $stem.s ]]; then
      "$as" -o "$work/native.o" "$stem.s"
      extra=("$work/native.o")
    fi
    "$filcc" -O1 -o "$work/runc" "$stem.c" "$work/m.so" "${extra[@]}"
    : >"$work/actual"
    n=$(wc -l <"$stem.expected")
    for ((i = 0; i < n; i++)); do
      if FUGC_SCRIBBLE=1 FUGC_VERIFY=1 "$work/runc" "$i" >"$work/r.out" 2>"$work/r.err"; then
        cat "$work/r.out" >>"$work/actual"
      elif grep -q 'filc safety error' "$work/r.err"; then
        echo "$(cat "$work/r.out")trap" >>"$work/actual"
      else
        echo "$(cat "$work/r.out")crash: $(head -c 200 "$work/r.err" | tr '\n' ' ')" >>"$work/actual"
      fi
    done 2>/dev/null
    if diff -u "$stem.expected" "$work/actual" >"$work/diff"; then
      same=$((same + 1))
    else
      echo "DIFFER $c $f"; head -20 "$work/diff"; status=1
    fi
  done
done
echo "shared: $same same, $skipped skipped"
exit $status
