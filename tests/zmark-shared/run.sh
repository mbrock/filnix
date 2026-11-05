# Runs zmark.c's cases. Expects ./zmark (Fil-C) and ./native-writer (native).
set -u
failures=0

ok() { # case: must exit 0 and print "<case> ok"-ish output
  if out=$(./zmark "$@" 2>&1); then
    echo "PASS $*"
  else
    echo "FAIL $* (exit $?)"; echo "$out" | tail -5; failures=$((failures + 1))
  fi
}

traps() { # case pattern: must not finish, and stderr must match pattern
  local c=$1 pat=$2
  out=$(./zmark "$c" 2>&1 | tr -d '\000'; exit "${PIPESTATUS[0]}")
  st=$?
  if [ $st -ne 0 ] && echo "$out" | grep -q "filc" && echo "$out" | grep -qE "$pat" \
      && ! echo "$out" | grep -qE "^$c (stored|marked|accessed)|^memmove-in ok|^hostile ok"; then
    echo "PASS $c traps: $(echo "$out" | grep -m1 -E "$pat" | cut -c1-140)"
  else
    echo "FAIL $c (exit $st, wanted /$pat/)"; echo "$out" | tail -8; failures=$((failures + 1))
  fi
}

ok postfork
# An unmarked segment behaves as today: the child traps on a post-fork pointer.
out=$(./zmark postfork-nomark 2>&1)
if echo "$out" | grep -q "child: p hasvalidcap=0" && echo "$out" | grep -q "filc safety error"; then
  echo "PASS postfork-nomark traps as before"
else
  echo "FAIL postfork-nomark"; echo "$out"; failures=$((failures + 1))
fi
ok unmarked
traps store-private "zmark_shared"
traps store-func "zmark_shared"
traps store-other "zmark_shared"
traps store-atomic-private "zmark_shared"
traps cas-private "zmark_shared"
ok atomics
ok memmove
ok race
ok memmove-in-small
ok memmove-in-big
traps memmove-in-deref "lower|upper|bounds"
traps munmap-deref "free|upper|bounds"
traps munmap-load "free|upper|bounds"
traps mark-aux "no pointer has been stored"
traps mark-private "MAP_SHARED"
traps mark-malloc "mapping"
traps mark-interior "start of a mapping"
ok hostile
traps hostile-private "lower|upper|bounds"
traps hostile-end "upper|bounds"
traps hostile-call "function|special|null object|bounds"
ok native "$PWD/native-writer"

echo "failures: $failures"
[ $failures -eq 0 ]
