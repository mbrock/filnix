#!/usr/bin/env bash
# Compile a glibc proof tree in dependency order with make, outside Nix,
# and record each file's time and peak memory.
#
#   . env.sh; build.sh TREE [JOBS]    # default: 8 jobs
#
# TREE.build/ gets times.txt ("seconds maxrssKB file" per line), make.log
# ("FAIL file" per failure, "DONE status" at the end), and logs/FILE.log
# with each compiler's output. Objects are written beside the sources.
# make -k continues after a failure, so one run reports every file that
# fails on its own account.
set -uo pipefail
tree=$(cd "$1" && pwd)
jobs=${2:-8}
out=$tree.build
mkdir -p "$out/logs"
rm -f "$out/times.txt" "$out/make.log"
cd "$tree" || exit 1
rocq dep -R "$PE_MODEL" Nanofil -R . Glibc $(find . -name '*.v' | sed 's|^\./||' | sort) >"$out/deps" 2>"$out/dep.err"
cat >"$out/Makefile" <<MK
all: \$(patsubst %.v,%.vo,\$(shell find . -name '*.v' | sed 's|^\./||'))
%.vo: %.v
	@mkdir -p $out/logs/\$(dir \$<)
	@/usr/bin/env time -f "%e %M \$<" -a -o $out/times.txt rocq c -q -R $PE_MODEL Nanofil -R . Glibc \$< >$out/logs/\$<.log 2>&1 || (echo "FAIL \$<"; exit 1)
include $out/deps
MK
make -k -j"$jobs" -f "$out/Makefile" >"$out/make.log" 2>&1
status=$?
echo "DONE $status" >>"$out/make.log"
grep -c . "$out/times.txt" | sed 's/$/ files compiled or attempted/'
grep '^FAIL' "$out/make.log"
exit $status
