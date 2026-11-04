#!/usr/bin/env bash
# Classify the ELF files in a closure as Fil-C, Fil-C runtime or native.
#
#   filc-audit [PATH]          # the closure of PATH, default /run/current-system
#   filc-audit --paths FILE    # the store paths listed in FILE, one per line
#   ... --allow FILE           # store paths whose native files are expected;
#                              # exit 1 if any other native file is found
#
# Reads each file's program headers and dynamic section with readelf: a
# Fil-C executable names the Fil-C loader (ld-fil1-*.so) as its interpreter,
# and a Fil-C executable or library needs libpizlo.so. That is what the
# loader acts on, so a native program that merely mentions those names, such
# as a compiler driver, is not counted as Fil-C. The runtime underneath
# (libpizlo, the loader and its yolo glibc) is native code that only Fil-C
# programs load; it is counted apart, as are kernel modules.
set -euo pipefail

root=/run/current-system pathsFile='' allowFile=''
while [ $# -gt 0 ]; do
  case $1 in
    --paths) pathsFile=$2; shift 2 ;;
    --allow) allowFile=$2; shift 2 ;;
    *) root=$1; shift ;;
  esac
done
if [ -n "$pathsFile" ]; then
  paths=$(cat "$pathsFile")
else
  paths=$(nix-store -qR "$root")
fi
declare -A allowed=()
if [ -n "$allowFile" ]; then
  while read -r p; do allowed[$p]=1; done <"$allowFile"
fi

filc=0 runtime=0 native=0 unexpected=0 kmod=0
declare -A nativePkgs=()

while IFS= read -r -d '' f; do
  case $f in
    *.ko | *.ko.xz | *.ko.zst) kmod=$((kmod + 1)); continue ;;
  esac
  headers=$(readelf -W -l -d "$f" 2>/dev/null) || continue # not ELF
  storePath=${f%"${f#/nix/store/*/}"}
  storePath=${storePath%/}
  pkg=${storePath#/nix/store/*-}
  case $pkg/${f##*/} in
    libpizlo-*/* | yolo-glibc*/* | */ld-fil1-*.so | */libpizlo.so | */libyolo*.so*)
      runtime=$((runtime + 1))
      continue
      ;;
  esac
  case $headers in
    *"interpreter: "*/ld-fil1-* | *"[libpizlo.so]"*) filc=$((filc + 1)) ;;
    *)
      native=$((native + 1))
      if [ -n "$allowFile" ] && [ -z "${allowed[$storePath]:-}" ]; then
        unexpected=$((unexpected + 1))
        pkg="$pkg  UNEXPECTED"
      fi
      nativePkgs[$pkg]=$((${nativePkgs[$pkg]:-0} + 1))
      ;;
  esac
done < <(xargs -r -I{} find {} -type f \( -perm -u+x -o -name '*.so*' -o -name '*.ko*' \) -print0 <<<"$paths")

total=$((filc + runtime + native))
echo "ELF files: $total (plus $kmod kernel modules)"
echo "  Fil-C:          $filc ($((total ? 100 * filc / total : 0))%)"
echo "  Fil-C runtime:  $runtime"
echo "  native:         $native${allowFile:+ ($unexpected unexpected)}"
echo
echo "Native files by package:"
for p in "${!nativePkgs[@]}"; do
  printf '%6d  %s\n' "${nativePkgs[$p]}" "$p"
done | sort -k1,1rn -k2
[ "$unexpected" -eq 0 ]
