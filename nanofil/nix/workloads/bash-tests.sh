#!/usr/bin/env bash
# bash-tests.sh TREE: run bash's own tests/run-* scripts against TREE/bash,
# one at a time, printing "NAME ok" when a script prints nothing (bash's
# convention for a pass), else "NAME differs" and what it printed, or
# "NAME timeout", after 1200 s (nanofil's plain bash runs ifs-posix's
# 6856 cases in over 300 s on a loaded builder).
# The builder's shell may export every variable and its options.
set +a; export -n SHELLOPTS BASHOPTS 2>/dev/null
tree=$(cd "$1" && pwd)
(cd "$tree" && make -s recho zecho printenv xcase >/dev/null && cp recho zecho printenv xcase tests/)
cd "$tree/tests"
export THIS_SH=$tree/bash BUILD_DIR=$tree PATH=$tree/tests:$PATH
base=${TMPDIR:-/tmp}
for x in run-*; do
  case $x in run-all|run-minimal|run-gprof|*.orig|*~) continue ;; esac
  t=$(mktemp -d "$base/bash-test.XXXXXX"); export TMPDIR=$t BASH_TSTOUT=$t/tstout
  timeout 1200 bash "$x" </dev/null >"$t/out" 2>&1; rc=$?
  # Whether a writer into a closed pipe reports EPIPE is timing: filcc's
  # bash printed comsub.tests:90's and lastpipe.tests:46's "echo: write
  # error: Broken pipe" in some runs, beside a nanofil bash that did not.
  # Drop those lines, and the diff's hunk headers if nothing else is left.
  sed -E -i '/^< .*: write error: Broken pipe$/d' "$t/out"
  grep -qvE '^[0-9]+(,[0-9]+)?[acd][0-9]+(,[0-9]+)?$' "$t/out" || : >"$t/out"
  if [ $rc = 124 ]; then r=timeout; elif [ -s "$t/out" ]; then r=differs; else r=ok; fi
  echo "${x#run-} $r"
  # What a failing script printed, its temporary directory, the tree's
  # path and process ids normalized, for diagnosis: it is not compared,
  # since some of it is timing (read -t, the interleaving of stdout and
  # stderr, and trap8.sub's SIGCHLDs, which the kernel may merge: filcc's
  # bash printed three CHLDs of four in 2 of 64 concurrent runs).
  sed -E -e "s|$t|TMP|g" -e 's#(TMP/[A-Za-z_.]*-)[0-9]+#\1PID#g' -e "s|$tree|TREE|g" \
    -e 's/process group \([0-9]+\)/process group (PID)/' \
    -e 's/^/    | /' "$t/out"
  rm -rf "$t"
done
