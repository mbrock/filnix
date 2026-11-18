#!/usr/bin/env bash
# Compile a flat glibc proof tree against an abstract runtime and require
# that every file compiles.
#
#   . env.sh; abstract-general.sh TREE OUT [JOBS]    # default: 8 jobs
#
# TREE has the sealed binding of Fix.v. OUT must not exist. The check
# copies the sources of TREE to OUT/glibc, replaces the one runtime
# binding by "Declare Module R : Runtime.", omits Hello's interpreter
# corollary, and compiles the remaining files with build.sh.
# A file that does not compile relies on the interpreter's definitions,
# and the check fails.
#
# OUT/report.txt names every file that failed, and OUT/glibc.build holds
# the logs and times of build.sh.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tree=$(cd "${1:?usage: abstract-general.sh TREE OUT [JOBS]}" && pwd)
out=${2:?usage: abstract-general.sh TREE OUT [JOBS]}
jobs=${3:-8}
if [ -e "$out" ]; then
  echo "abstract-general: refusing existing output directory $out" >&2
  exit 2
fi
mkdir -p "$out"
out=$(cd "$out" && pwd)
cp -r "$tree" "$out/glibc"
find "$out/glibc" \( -name '*.vo*' -o -name '*.glob' -o -name '.*.aux' \) -delete
signature='Module Type StartRuntime := Runtime'
binding='Module R : StartRuntime := InterpRuntime.'
if [ "$(grep -cxF "$signature" "$out/glibc/Fix.v")" != 1 ] ||
   [ "$(grep -cxF "$binding" "$out/glibc/Fix.v")" != 1 ]; then
  echo "abstract-general: Fix.v must seal the interpreter runtime exactly once" >&2
  exit 2
fi
sed -i "/^$signature\$/,/^$binding\$/c\\Declare Module R : Runtime." "$out/glibc/Fix.v"
rm -f "$out/glibc/hello/HelloInterpNeverPanics.v"
bash "$here/build.sh" "$out/glibc" "$jobs" >"$out/build.log" 2>&1
(
  cd "$out/glibc" || exit 1
  find . -name '*.v' | sed 's|^\./||' | sort >"$out/all.txt"
  while read -r f; do
    [ -f "${f%.v}.vo" ] || echo "$f"
  done <"$out/all.txt" >"$out/failed.txt"
)
status=0
sed 's/^/FAIL does not compile against the abstract runtime: /' "$out/failed.txt" >"$out/report.txt"
if [ -s "$out/report.txt" ]; then
  status=1
fi
printf '@@abstract-general %d files, %d compiled\n' \
  "$(grep -c . "$out/all.txt")" \
  "$(($(grep -c . "$out/all.txt") - $(grep -c . "$out/failed.txt")))" | tee -a "$out/report.txt"
grep '^FAIL' "$out/report.txt" >&2
exit "$status"
