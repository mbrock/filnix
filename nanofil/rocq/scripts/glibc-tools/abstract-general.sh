#!/usr/bin/env bash
# Compile a flat glibc proof tree against an abstract runtime and require
# that the files which do not compile are exactly the listed ones.
#
#   . env.sh; abstract-general.sh TREE OUT [JOBS]    # default: 8 jobs
#
# TREE has the sealed binding of Fix.v and concrete objects previously
# compiled with a transparent binding. OUT must not exist. The check
# copies the sources of TREE to OUT/glibc, replaces the one runtime
# binding by "Declare Module R : Runtime.", and compiles with build.sh.
#
# TREE/runtime-concrete.txt lists the files that need the interpreter's
# runtime, one path per line, with "#" comments. The check fails when
#
#   - a file that is not listed does not compile, which happens when a
#     proof starts to rely on the interpreter's definitions or imports a
#     listed file;
#   - a listed file compiles, so that no file can leave the check by
#     being listed without need;
#   - a listed file does not exist, or has no object in TREE. The two
#     trees differ only in the runtime binding, so a file that compiles
#     in TREE and not in the copy fails because of the runtime and for
#     no other reason;
#   - a listed file that imports no listed file is not rejected by an
#     error of the compiler itself. tests/rocq_reject.py compiles it
#     again and refuses a timeout, a signal, a status other than 1, and
#     an error that is not located in the file.
#
# OUT/report.txt names every file on the wrong side, and OUT/glibc.build
# holds the logs and times of build.sh.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tree=$(cd "${1:?usage: abstract-general.sh TREE OUT [JOBS]}" && pwd)
out=${2:?usage: abstract-general.sh TREE OUT [JOBS]}
jobs=${3:-8}
reject=$here/../../../tests/rocq_reject.py
if [ -e "$out" ]; then
  echo "abstract-general: refusing existing output directory $out" >&2
  exit 2
fi
mkdir -p "$out"
out=$(cd "$out" && pwd)
cp -r "$tree" "$out/glibc"
find "$out/glibc" \( -name '*.vo*' -o -name '*.glob' -o -name '.*.aux' \) -delete
binding='Module R : Runtime := InterpRuntime.'
if [ "$(grep -cxF "$binding" "$out/glibc/Fix.v")" != 1 ]; then
  echo "abstract-general: Fix.v must seal the interpreter runtime exactly once" >&2
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
  comm -12 "$out/all.txt" "$out/listed.txt" | while read -r f; do
    if [ ! -f "$tree/${f%.v}.vo" ]; then
      echo "FAIL listed file has no object in TREE, so it does not compile at the interpreter's runtime either: $f"
    fi
    # make starts no compiler for a file whose import failed, so only a
    # listed file with no listed import has a rejection to examine.
    if grep "^${f%.v}\.vo " "$out/glibc.build/deps" | tr ' ' '\n' | sed -n 's/\.vo$/.v/p' |
      grep -vxF "$f" | grep -qxFf "$out/listed.txt"; then
      continue
    fi
    mkdir -p "$out/rejections/$(dirname "$f")"
    if ! (cd "$out/glibc" && python3 "$reject" --file "$f" --timeout "${PE_REJECT_TIMEOUT:-900}" \
      --log "$out/rejections/$f.log" -- rocq c -q -R "$PE_MODEL" Nanofil -R . Glibc "$f") \
      >"$out/rejections/$f.verdict" 2>&1; then
      echo "FAIL listed file is not rejected by a compiler error ($(sed -n 's/^rocq_reject: refused: //p' "$out/rejections/$f.verdict")): $f"
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
