#!/usr/bin/env bash
# Compile a copy of nanofil/rocq (theories and glibc together) with whichever
# rocq is on PATH, and record each file's time, peak memory and sentence
# timings. The Rocq 9.3 comparison runs this once per version on identical
# copies of the tree, with the same job count, one after the other.
#
#   measure.sh TREE JOBS [TARGET...]    # TARGET: theories, libio or all (default)
#
# TREE.build/ gets times.txt ("seconds maxrssKB file" per line), make.log
# ("FAIL file" per failure), and logs/FILE.log with `rocq c -time` output.
# make -k keeps going, so files that fail on their own account all show up;
# files whose imports failed are not attempted.
set -uo pipefail
tree=$(cd "$1" && pwd)
jobs=$2
shift 2
targets=${*:-all}
out=$tree.build
mkdir -p "$out/logs"
cd "$tree" || exit 1
export OCAMLRUNPARAM=o=200
files=$(find theories glibc -name '*.v' | sort)
rocq dep -R theories Nanofil -R glibc Glibc $files >"$out/deps" 2>"$out/dep.err"
cat >"$out/Makefile" <<MK
all: \$(patsubst %.v,%.vo,\$(shell find theories glibc -name '*.v'))
theories: \$(patsubst %.v,%.vo,\$(shell find theories -name '*.v'))
libio: \$(patsubst %.v,%.vo,\$(shell find glibc/libio -name '*.v'))
%.vo: %.v
	@mkdir -p $out/logs/\$(dir \$<)
	@/usr/bin/env time -f "%e %M \$<" -a -o $out/times.txt rocq c -q -time -R theories Nanofil -R glibc Glibc \$< >$out/logs/\$<.log 2>&1 || (echo "FAIL \$<"; exit 1)
include $out/deps
MK
start=$(date +%s)
make -k -j"$jobs" -f "$out/Makefile" $targets >>"$out/make.log" 2>&1
status=$?
echo "DONE $status $targets wall=$(( $(date +%s) - start ))s" >>"$out/make.log"
grep '^FAIL\|^DONE' "$out/make.log"
exit $status
