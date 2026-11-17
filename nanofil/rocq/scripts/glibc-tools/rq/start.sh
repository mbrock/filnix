#!/usr/bin/env bash
# Start (or restart) a persistent Rocq REPL on a glibc proof file and load
# the file up to a line, so that the next tactics can be tried in seconds
# instead of recompiling the file.
#
#   . nanofil/rocq/scripts/glibc-tools/env.sh
#   rq/start.sh FILE LINE [TREE]      # FILE relative to TREE (default nanofil/rocq/glibc)
#   rq/rq.py 'iIntros "H". step.'     # try tactics; an error rolls the chunk back
#   rq/rq.py -f TREE/FILE A B         # replay lines A..B of the file after editing them
#   kill "$(cat /tmp/rq.pid)"         # stop it; never pkill -f
#
# The file's imports must already be compiled in TREE (warm.sh, then
# build.sh or one.sh for anything you edited). The server uses the same
# load path as build.sh. Load errors are printed at the end.
set -u
here=$(cd "$(dirname "$0")" && pwd)
tree=$(cd "${3:-$(git -C "$here" rev-parse --show-toplevel)/nanofil/rocq/glibc}" && pwd)
sock=${RQ_SOCK:-/tmp/rq.sock}
if [ -f /tmp/rq.pid ]; then kill "$(cat /tmp/rq.pid)" 2>/dev/null; sleep 0.5; fi
cd "$tree" || exit 1
nohup python3 "$here/server.py" "$sock" -q -R "$PE_MODEL" Nanofil -R . Glibc >/tmp/rq.server.log 2>&1 &
echo $! >/tmp/rq.pid
sleep 1
RQ_SOCK=$sock python3 "$here/rq.py" -f "$1" 1 "$2" >/tmp/rq.load 2>&1
grep -n "Error" -A3 /tmp/rq.load | head -20
tail -2 /tmp/rq.load
