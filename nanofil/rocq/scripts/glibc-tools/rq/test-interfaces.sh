#!/usr/bin/env bash
# Run after sourcing env.sh. Exercise cold open, transitive reload, failed
# imports, and scratch-only edits through the same CLI that an author uses.
set -euo pipefail
rq=$(cd "$(dirname "$0")" && pwd)/rq
work=$(mktemp -d)
export RQ_DIR=$work/sessions
trap '"$rq" stop all >/dev/null; rm -rf "$work"' EXIT
mkdir "$work/src" "$work/cache"
if [[ -e $PE_CACHE/rq-worker ]]; then
    ln -s "$(realpath "$PE_CACHE/rq-worker")" "$work/cache/rq-worker"
    touch -hr "$PE_CACHE/rq-worker" "$work/cache/rq-worker"
fi
export PE_CACHE=$work/cache
cat > "$work/src/Base.v" <<'EOF'
Definition value := 1.
Lemma opaque_proof : False.
Proof. exact I. Qed.
EOF
echo 'From Glibc Require Import Base. Definition seen := value.' > "$work/src/Mid.v"
echo 'From Glibc Require Import Mid. Goal seen = 1. Proof. reflexivity. Qed.' > "$work/src/Leaf.v"
echo 'Definition broken := true + 1.' > "$work/src/Unrelated.v"

"$rq" verify --tree "$work/src" Leaf.v
if "$rq" verify --tree "$work/src" Base.v; then echo "verify skipped the target proof" >&2; exit 1; fi
"$rq" open --tree "$work/src" Leaf.v
reply=$("$rq" reload R1 --json)
python3 -c 'import json,sys; r=json.loads(sys.argv[1]); assert r["reused"] > 0 and not r["committed"] and "restarted_for" not in r, r' "$reply"
"$rq" step R1 -e 'Definition scratch := 3.'
sed -i 's/value := 1/value := 2/' "$work/src/Base.v"
if "$rq" reload R1; then echo "reload accepted a proof of the old value" >&2; exit 1; fi
grep -Fq 'Definition scratch := 3.' "$RQ_DIR/R1/dropped.v"
sed -i 's/seen = 1/seen = 2/' "$work/src/Leaf.v"
"$rq" reload R1
echo 'Definition value := missing_name.' > "$work/src/Base.v"
if "$rq" reload R1; then echo "reload accepted a broken import" >&2; exit 1; fi
echo 'Definition value := 2.' > "$work/src/Base.v"
"$rq" reload R1
[ -z "$(find "$work/src" \( -name '*.vos' -o -name '*.vo' \) -print -quit)" ]
