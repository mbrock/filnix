#!/usr/bin/env bash
# The extracted Rocq validator as a gate on what the compiler emits
# (docs/rocq.md, the validator and its gate): for each file, the checked
# module nanofil gives its backend (`nanofil checked-terms`, with
# $NANOFIL_OPT, -O by default) goes to the model's --module mode, which
# judges it as Validate.v's [valid] does, the validator
# [valid_no_unchecked] is proved sound for. A FILE.terms is that module
# already printed (nanofil-cc's terms mode, nix/rocq-gate.nix). A C file
# compiles as tests/progtest.sh compiles it: its "// cflags:" line
# preprocesses it with filcc, and "// no-vectors" adds --no-vectors.
#
#   MODEL=.../bin/nanofil-model gate.sh FILE.c|FILE.ir|FILE.terms...
#
# Prints one "@@nanofil-gate VERDICT FILE SECONDS DETAIL" line per file:
# valid; invalid, with the items the model rejects; outside, with the
# functions outside the model's subset (the theorem says nothing about
# such a module, so it does not fail); plain, an IR module without
# Fil-C; or refused, where nanofil does not compile the file. Exits 1 if
# any module is invalid or the model cannot read it.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
nanofil="$here/../bin/nanofil"
model=${MODEL:-nanofil-model}
read -r -a opt <<<"${NANOFIL_OPT--O}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

status=0
for f in "$@"; do
  t0=${EPOCHREALTIME/./}
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  report() {
    local ms=$(( (${EPOCHREALTIME/./} - t0) / 1000 ))
    printf '@@nanofil-gate %s %s %d.%03d %s\n' "$1" "$f" $((ms / 1000)) $((ms % 1000)) "${2:-}"
  }
  terms=$f
  if [[ $f != *.terms ]]; then
    terms=$work/module.terms input=$f flags=() std=c17 common= math_errno=
    if [[ $f == *.c ]]; then
      read -r -a cflags <<<"$(sed -n 's|^// cflags: ||p' "$f")"
      if [[ " ${cflags[*]} " =~ \ -fcommon\  ]]; then common=1; fi
      if [[ " ${cflags[*]} " =~ \ -std=(c|gnu)(23|2x)\  ]]; then std=c23; fi
      if [[ " ${cflags[*]} " =~ \ (-std=(c|gnu)(89|90)|-ansi|-fgnu89-inline)\  ]]; then std=gnu89; fi
      if [[ " ${cflags[*]} " =~ \ -fno-math-errno\  ]]; then math_errno=0; fi
      if [ ${#cflags[@]} != 0 ]; then
        input=$work/input.i
        "${FILCC:?set FILCC to a filcc clang}" "${cflags[@]}" -E -o "$input" "$f"
      fi
      if grep -q '^// no-vectors' "$f"; then flags+=(--no-vectors); fi
    fi
    if ! (cd "$src" && NANOFIL_STD=$std NANOFIL_COMMON=$common NANOFIL_MATH_ERRNO=$math_errno \
          "$nanofil" ${opt[@]+"${opt[@]}"} ${flags[@]+"${flags[@]}"} checked-terms "$input" </dev/null) >"$terms" 2>"$work/err"; then
      if grep -q 'needs a Fil-C module' "$work/err"; then report plain; else
        report refused "$(grep -v '^$' "$work/err" | head -1 | cut -c1-200)"
      fi
      continue
    fi
  fi
  "$model" --module <"$terms" >"$work/verdict" 2>&1
  rc=$?
  verdict=$(cut -c1-2000 "$work/verdict")
  case $rc:$verdict in
    0:valid\(*) report valid "$verdict" ;;
    0:outside\(*) report outside "$verdict" ;;
    1:invalid\(*) report invalid "$verdict"; status=1 ;;
    *) report error "exit $rc: $verdict"; status=1 ;;
  esac
done
exit $status
