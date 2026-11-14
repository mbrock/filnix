#!/usr/bin/env bash
# Retain both sides of an unlanded tactic stage independently of later stages.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
source=${1:?usage: tactics-boundary.sh ORIGINAL NEW_DIRECTORY}
out=${2:?usage: tactics-boundary.sh ORIGINAL NEW_DIRECTORY}
boundary=${3:-30}
test ! -e "$out"
mkdir -p "$out"
cp -r "$source" "$out/before"
find "$out/before" \( -name '*.vo*' -o -name '*.glob' -o -name '.*.aux' \) -delete
for stage in "$here"/stages/*; do
  case "$stage" in *.py|*.sh) ;; *) continue ;; esac
  if [ -f "$here/stages/landed.txt" ] && grep -qxF "$(basename "$stage")" "$here/stages/landed.txt"; then
    continue
  fi
  if [[ $(basename "$stage") == "$boundary"-* ]]; then
    if [ "$boundary" = 60 ]; then
      cp -r "$here/overlay/." "$out/before/"
      cp -r "$out/before" "$out/after"
      python3 -I "$stage" "$out/after"
      exit 0
    fi
    cp "$here/overlay/GlibcEnv.v" "$out/before/GlibcEnv.v"
    cp -r "$out/before" "$out/after"
    python3 -I "$stage" "$out/after"
    cp "$here/overlay/GlibcEnv.v" "$out/after/GlibcEnv.v"
    cp "$here/overlay/GlibcTactics.v" "$out/after/GlibcTactics.v"
    cp "$here/overlay/libio/LibioTactics.v" "$out/after/libio/LibioTactics.v"
    exit 0
  fi
  case "$stage" in
    *.py) python3 -I "$stage" "$out/before" ;;
    *) bash "$stage" "$out/before" ;;
  esac
done
echo "No unlanded stage $boundary found" >&2
exit 1
