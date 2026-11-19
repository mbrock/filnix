#!/usr/bin/env bash
# Compile only what the given files import, in dependency order, so that
# a file you are about to work on can be loaded without building the
# whole tree. The files themselves are not compiled.
#
#   . env.sh; imports.sh FILE... [-- TREE]   # FILE relative to TREE (default nanofil/rocq/glibc)
#
# Make reuses objects that are current with their sources and imports.
# A failing import prints "FAIL file" and the head of its log.
set -uo pipefail
files=()
tree=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)/nanofil/rocq/glibc
while [ $# -gt 0 ]; do
  if [ "$1" = -- ]; then tree=$2; shift 2; else files+=("$1"); shift; fi
done
tree=$(cd "$tree" && pwd)
out=$tree.build
mkdir -p "$out/logs"
cd "$tree" || exit 1
rocq dep -R "$PE_MODEL" Nanofil -R . Glibc $(find . -name '*.v' | sed 's|^\./||' | sort) >"$out/deps" 2>"$out/dep.err"
cat >"$out/Makefile.imports" <<MK
%.vo: %.v
	@mkdir -p $out/logs/\$(dir \$<)
	@rocq c -q -R $PE_MODEL Nanofil -R . Glibc \$< >$out/logs/\$<.log 2>&1 || (echo "FAIL \$<"; head -20 $out/logs/\$<.log; exit 1)
include $out/deps
MK
targets=$(for f in "${files[@]}"; do
  grep "^${f%.v}.vo " "$out/deps" | head -1 | cut -d: -f2 | tr ' ' '\n' | grep '\.vo$' | grep -v "^${f%.v}.vo$"
done | sort -u)
[ -n "$targets" ] || { echo "imports.sh: nothing to build"; exit 0; }
make -k -j"$(nproc)" -f "$out/Makefile.imports" $targets | grep -v "is up to date"
status=${PIPESTATUS[0]}
echo "imports.sh: $(echo "$targets" | wc -l) imports, make exit $status"
exit $status
