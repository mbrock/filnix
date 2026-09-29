#!/usr/bin/env bash
# Classify the ELF files in a closure as Fil-C or native.
#
#   filc-audit [PATH]    # default: /run/current-system
#
# A Fil-C executable names the Fil-C loader (ld-fil1-*.so) as its
# interpreter, and a Fil-C library needs libpizlo, so both strings appear in
# the file. Kernel modules are counted apart; they are the kernel's.
set -euo pipefail

root=${1:-/run/current-system}
filc=0 native=0 kmod=0
declare -A nativePkgs=()

while IFS= read -r -d '' f; do
  [ "$(head -c 4 "$f" 2>/dev/null | od -An -c | tr -d ' ')" = '177ELF' ] || continue
  case $f in
    *.ko | *.ko.xz | *.ko.zst) kmod=$((kmod + 1)); continue ;;
  esac
  if grep -qaE 'ld-fil1-|libpizlo\.so' "$f"; then
    filc=$((filc + 1))
  else
    native=$((native + 1))
    pkg=${f#/nix/store/*-}
    pkg=${f#/nix/store/}
    pkg=${pkg%%/*}
    nativePkgs[${pkg#*-}]=$(( ${nativePkgs[${pkg#*-}]:-0} + 1 ))
  fi
done < <(nix-store -qR "$root" | xargs -I{} find {} -type f \( -perm -u+x -o -name '*.so*' \) -print0)

total=$((filc + native))
echo "ELF files: $total (plus $kmod kernel modules)"
echo "  Fil-C:  $filc ($(( total ? 100 * filc / total : 0 ))%)"
echo "  native: $native"
echo
echo "Native files by package:"
for p in "${!nativePkgs[@]}"; do
  printf '%6d  %s\n' "${nativePkgs[$p]}" "$p"
done | sort -rn
