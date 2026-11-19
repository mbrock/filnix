#!/usr/bin/env bash
# Test abstract-general.sh on small trees: one tree that passes, one
# with a file that needs the interpreter's runtime, and one whose Fix.v
# has no sealed binding.
#
#   . env.sh; abstract-general-test.sh
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
failures=0

# tree NAME: a sealed Fix.v and a file that uses only the signature.
tree() {
  mkdir -p "$tmp/$1/sub" "$tmp/$1/base"
  cp "$here/../../glibc/base/Fix.v" "$tmp/$1/base/Fix.v"
  cat >"$tmp/$1/sub/General.v" <<'EOT'
From Glibc Require Import Fix.
Lemma general (s : R.state) : s = s.
Proof. reflexivity. Qed.
EOT
}

# expect NAME STATUS PATTERN: the check of tree NAME exits with STATUS,
# and for a failure its report has a line that matches PATTERN.
expect() {
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

tree needs-interpreter
cat >"$tmp/needs-interpreter/Concrete.v" <<'EOT'
From Stdlib Require Import ZArith.
From Glibc Require Import Fix.
Definition cursor : R.state := 4294969872%Z.
EOT
tree passes
mkdir -p "$tmp/passes/hello"
cp "$tmp/needs-interpreter/Concrete.v" "$tmp/passes/hello/HelloInterpNeverPanics.v"
expect passes 0 '@@abstract-general 2 files, 2 compiled'
expect needs-interpreter 1 'abstract runtime: Concrete.v'

tree unbound
sed -i '/^Module R : StartRuntime := InterpRuntime\.$/d' "$tmp/unbound/base/Fix.v"
expect unbound 2 ''

if [ "$failures" != 0 ]; then
  echo "$failures abstract-general tests failed"
  exit 1
fi
echo 'abstract-general tests passed'
