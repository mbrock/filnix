#!/usr/bin/env bash
# Test abstract-general.sh on small trees: one tree that passes, and one
# tree for each way in which a file can be on the wrong side of
# runtime-concrete.txt.
#
#   . env.sh; abstract-general-test.sh
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
failures=0

# tree NAME: a general file, and a file that needs the interpreter.
tree() {
  mkdir -p "$tmp/$1/sub"
  cat >"$tmp/$1/Fix.v" <<'EOF'
From Nanofil Require Import Runtime.
Module R := InterpRuntime.
EOF
  cat >"$tmp/$1/General.v" <<'EOF'
From Glibc Require Import Fix.
Lemma general (s : R.state) : s = s.
Proof. reflexivity. Qed.
EOF
  cat >"$tmp/$1/sub/Concrete.v" <<'EOF'
From Stdlib Require Import ZArith.
From Glibc Require Import Fix General.
Definition cursor : R.state := 4294969872%Z.
EOF
  printf '# The cursor is a number.\nsub/Concrete.v\n' >"$tmp/$1/runtime-concrete.txt"
}

# expect NAME STATUS PATTERN: the check of tree NAME exits with STATUS,
# and for a failure its report has a line that matches PATTERN.
expect() {
  bash "$here/build.sh" "$tmp/$1" 4 >/dev/null 2>&1
  bash "$here/abstract-general.sh" "$tmp/$1" "$tmp/$1.out" 4 >"$tmp/$1.log" 2>&1
  local status=$?
  if [ "$status" != "$2" ]; then
    echo "FAIL $1: exit $status, expected $2"
    cat "$tmp/$1.log"
    failures=$((failures + 1))
  elif [ -n "$3" ] && ! grep -q "$3" "$tmp/$1.out/report.txt"; then
    echo "FAIL $1: the report has no line matching: $3"
    cat "$tmp/$1.out/report.txt"
    failures=$((failures + 1))
  else
    echo "ok   $1"
  fi
}

tree passes
expect passes 0 ''

tree general-needs-interpreter
cat >>"$tmp/general-needs-interpreter/General.v" <<'EOF'
From Stdlib Require Import ZArith.
Definition cursor : R.state := 1%Z.
EOF
expect general-needs-interpreter 1 'not listed: General.v'

tree general-imports-listed
cat >"$tmp/general-imports-listed/Importer.v" <<'EOF'
From Glibc Require Import Concrete.
Lemma importer : True.
Proof. exact I. Qed.
EOF
expect general-imports-listed 1 'not listed: Importer.v'

tree listed-without-need
echo General.v >>"$tmp/listed-without-need/runtime-concrete.txt"
expect listed-without-need 1 'compiles against the abstract runtime; remove it from runtime-concrete.txt: General.v'

tree listed-missing
echo sub/Gone.v >>"$tmp/listed-missing/runtime-concrete.txt"
expect listed-missing 1 'does not exist: sub/Gone.v'

tree listed-fails-otherwise
echo 'Lemma broken : True. Proof. exact 0. Qed.' >"$tmp/listed-fails-otherwise/sub/Concrete.v"
expect listed-fails-otherwise 1 'has no object in TREE.*: sub/Concrete.v'

tree unbound
sed -i 's/^Module R := InterpRuntime\.$/Declare Module R : Runtime./' "$tmp/unbound/Fix.v"
expect unbound 2 ''

if [ "$failures" != 0 ]; then
  echo "$failures abstract-general tests failed"
  exit 1
fi
echo 'abstract-general tests passed'
