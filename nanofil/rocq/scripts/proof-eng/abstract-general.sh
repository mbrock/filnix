#!/usr/bin/env bash
# Compile a flat glibc proof tree against an abstract runtime and require
# that the files which do not compile are exactly the listed ones.
#
#   . env.sh; abstract-general.sh TREE OUT [JOBS]    # default: 8 jobs
#
# TREE is a flat tree: the output of apply.sh, or rocq/glibc of main after
# the first cutover. OUT must not exist. The check copies TREE to
# OUT/glibc, replaces the one runtime binding of Fix.v by
# "Declare Module R : Runtime.", and compiles every file with build.sh.
#
# TREE/runtime-concrete.txt lists the files that need the interpreter's
# runtime, one path per line, with "#" comments. The check fails when
#
#   - a file that is not listed does not compile, which happens when a
#     proof starts to rely on the interpreter's definitions or imports a
#     listed file;
#   - a listed file compiles, so that no file can leave the check by
#     being listed without need;
#   - a listed file fails for a reason other than a Fix.R field or a
#     listed import, or does not exist.
#
# OUT/report.txt names every file on the wrong side, and OUT/glibc.build
# holds the logs and times of build.sh.
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
binding='Module R := InterpRuntime.'
if [ "$(grep -cxF "$binding" "$out/glibc/Fix.v")" != 1 ]; then
  echo "abstract-general: Fix.v must bind the interpreter runtime exactly once" >&2
  exit 2
fi
sed -i "s/^$binding\$/Declare Module R : Runtime./" "$out/glibc/Fix.v"
list=$tree/runtime-concrete.txt
if [ ! -f "$list" ]; then
  echo "abstract-general: $list is missing" >&2
  exit 2
fi
sed 's/#.*//; s/[[:space:]]*$//; /^$/d' "$list" | sort -u >"$out/listed.txt"
bash "$here/build.sh" "$out/glibc" "$jobs" >"$out/build.log" 2>&1
(
  cd "$out/glibc" || exit 1
  find . -name '*.v' | sed 's|^\./||' | sort >"$out/all.txt"
  while read -r f; do
    [ -f "${f%.v}.vo" ] || echo "$f"
  done <"$out/all.txt" >"$out/failed.txt"
)
status=0
{
  comm -13 "$out/all.txt" "$out/listed.txt" | sed 's/^/FAIL listed file does not exist: /'
  comm -23 "$out/failed.txt" "$out/listed.txt" |
    sed 's/^/FAIL does not compile against the abstract runtime and is not listed: /'
  comm -13 "$out/failed.txt" "$out/listed.txt" | grep -xFf "$out/all.txt" |
    sed 's/^/FAIL listed file compiles against the abstract runtime; remove it from runtime-concrete.txt: /'
  # A listed file must fail on a runtime field, or on the import of
  # another listed file, in which case make never starts its compiler.
  comm -12 "$out/failed.txt" "$out/listed.txt" | while read -r f; do
    log=$out/glibc.build/logs/$f.log
    if [ -f "$log" ] && ! grep -q 'Fix\.R\.' "$log"; then
      echo "FAIL listed file fails without naming a Fix.R field: $f"
    fi
  done
} >"$out/report.txt"
if [ -s "$out/report.txt" ]; then
  status=1
fi
printf '@@abstract-general %d files, %d compiled, %d listed\n' \
  "$(grep -c . "$out/all.txt")" \
  "$(($(grep -c . "$out/all.txt") - $(grep -c . "$out/failed.txt")))" \
  "$(grep -c . "$out/listed.txt")" | tee -a "$out/report.txt"
cat "$out/report.txt" | grep '^FAIL' >&2
exit "$status"
