#!/usr/bin/env bash
# Assemble the playground's files: nanofil's sources, the driver, the
# frozen preprocessor profile and the headers it reaches.
#
#   build.sh OUT          the page in OUT: index.html and its scripts,
#                         dterm's stylesheet and fs.json, which maps each
#                         virtual path to its text; with SWIPL_WASM (the
#                         dist/swipl directory of the swipl-wasm npm
#                         package) also OUT/swipl
#   build.sh OUT --native also OUT/root/..., a real tree for native runs
#
# Needs FILCC (Fil-C clang) and SWIPL. Headers are those that HEADERS
# (default headers.c beside this script) includes, by clang -M.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
nanofil=$(cd "$here/../.." && pwd)
out=$1
native=${2:-}
mkdir -p "$out"
out=$(cd "$out" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
root=$tmp/root

mkdir -p "$root/nanofil/src/swi"
cp "$nanofil"/src/*.pl "$root/nanofil/src/"
cp "$nanofil"/src/swi/*.pl "$root/nanofil/src/swi/"
cp "$here/play.pl" "$here/play_view.pl" "$here/load_swi.pl" "$root/nanofil/src/"
mkdir -p "$root/nanofil/web"
cp "$nanofil/web/dterm.pl" "$root/nanofil/web/"
mkdir -p "$root/nanofil/play-lib"
cp "$here/wasm/process.pl" "$root/nanofil/play-lib/"

# profile.pl runs beside the sources it loads, in a scratch copy.
profile() {
  rm -rf "$tmp/src"; cp -r "$nanofil/src" "$tmp/src"; cp "$here/profile.pl" "$tmp/src/"
  (cd "$tmp/src" && "$nanofil/bin/nanofil" --script profile.pl "$@" </dev/null)
}
profile "$root/nanofil/src/profile.data" 2>"$tmp/dirs"

"${FILCC:-filcc}" -M "${HEADERS:-$here/headers.c}" | tr ' \\' '\n\n' | grep '^/' | sort -u >"$tmp/deps"
while read -r _ n dir; do
  while read -r f; do
    case $f in
      "$dir"/*) rel=${f#"$dir"/}; mkdir -p "$root/inc/$n/$(dirname "$rel")"; cp "$f" "$root/inc/$n/$rel" ;;
    esac
  done <"$tmp/deps"
done <"$tmp/dirs"

python3 - "$root" "$out/fs.json" <<'EOF'
import json, os, sys
root, dest = sys.argv[1], sys.argv[2]
fs = {}
for d, _, files in os.walk(root):
    for f in files:
        p = os.path.join(d, f)
        with open(p, encoding="utf-8", errors="surrogateescape") as h:
            fs["/" + os.path.relpath(p, root)] = h.read()
with open(dest, "w") as h:
    json.dump(fs, h, separators=(",", ":"), sort_keys=True)
EOF

cp "$here"/{index.html,play.css,play.js,worker.js} "$nanofil"/web/{dterm.css,dterm.js} "$out/"
if [ -n "${SWIPL_WASM:-}" ]; then
  mkdir -p "$out/swipl"
  cp "$SWIPL_WASM"/swipl-web.{js,wasm,data} "$out/swipl/"
fi

if [ "$native" = --native ]; then
  rm -rf "$out/root"
  cp -r "$root" "$out/root"
  profile "$out/root/nanofil/src/profile.data" "$out/root" 2>/dev/null
fi
echo "$out/fs.json: $(wc -c <"$out/fs.json") bytes, $(find "$root" -type f | wc -l) files"
