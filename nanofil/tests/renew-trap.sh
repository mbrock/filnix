#!/usr/bin/env bash
# Check renewal, range guards, hoisted bounds, half checks and forward
# facts keep each trap's text (docs/m7.md, rounds 4 and 5;
# docs/bounds.md; docs/half.md; docs/forward.md): every
# tests/c/prog/renew-*.c, guard-*.c, hoist-*.c, half-*.c and forward-*.c
# is built by nanofil -O, sharing nothing, with reference checks and with
# --checks=renew, guard, hoist, half or forward, half-*.c and forward-*.c
# also with combined and -O's default shared check parts, and
# both runs must agree on stdout, the exit
# status and the whole stderr (the safety error, its pointer's state,
# expected bytes and origins) with addresses and the pid masked. The
# renew build must have fewer full checks (renewals), the guard build a
# guarded access, the hoist build a limit, the half build fewer null
# tests than renewal alone and the forward build fewer check tests than
# renewal alone, or the comparison would show nothing.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
status=0
for f in "$here"/c/prog/renew-*.c "$here"/c/prog/guard-*.c "$here"/c/prog/hoist-*.c "$here"/c/prog/half-*.c "$here"/c/prog/forward-*.c; do
  name=$(basename "$f" .c)
  mode=${name%%-*}
  read -r -a args <<<"$(sed -n 's|^// args: ||p' "$f")"
  builds="reference $mode"
  [[ $mode == half || $mode == forward ]] && builds="$builds renew combined"
  for c in $builds; do
    # The same file name in both, since origins name the executable.
    d=$work/$c; mkdir -p "$d"
    share=--share=none; [[ $c == combined ]] && share=
    (cd "$here/../src" && ../bin/nanofil -O --checks=$c $share cc "$f" </dev/null) >"$d/$name.s"
    as -o "$d/$name.o" "$d/$name.s"
    "$filcc" -o "$d/$name" "$d/$name.o"
    set +e
    bash -c '"$@" >"$0.out" 2>"$0.err"; exit $?' "$d/$name" ${RUN_ENV:-} "$d/$name" "${args[@]}" 2>/dev/null
    echo "exit $?" >>"$d/$name.out"
    set -e
    sed -E 's/0x[0-9a-f]+/0x?/g; s/^\[[0-9]+\]/[pid]/' "$d/$name.err" >>"$d/$name.out"
  done
  full() { grep -cE '^\s*jz\s+\.L.*\.\.fail\.' "$1" || true; }
  # A guarded access's full check is out of line, after a .full label.
  guarded() { grep -cE '\.full:$' "$1" || true; }
  # A hoisted check's limit is computed before the loop, ending at a
  # .limit label.
  limited() { grep -cE '\.limit:$' "$1" || true; }
  # Every jump to a check's failure block: full checks and renewals.
  tests() { grep -cE '^\s*j[a-z]+\s+\.L.*\.\.fail\.' "$1" || true; }
  if [[ $mode == guard ]] && (( $(guarded "$work/guard/$name.s") == 0 )); then
    echo "$name: no guarded access in the guard build"; status=1
  elif [[ $mode == hoist ]] && (( $(limited "$work/hoist/$name.s") == 0 )); then
    echo "$name: no limit in the hoist build"; status=1
  elif [[ $mode == half ]] && (( $(full "$work/half/$name.s") >= $(full "$work/renew/$name.s") )); then
    echo "$name: no half check in the half build"; status=1
  elif [[ $mode == forward ]] && (( $(tests "$work/forward/$name.s") >= $(tests "$work/renew/$name.s") )); then
    echo "$name: no more reuse in the forward build than with renew"; status=1
  elif [[ $mode == renew ]] && (( $(full "$work/renew/$name.s") >= $(full "$work/reference/$name.s") )); then
    echo "$name: no renewal in the $mode build"; status=1
  elif ! grep -q 'filc safety error' "$work/reference/$name.out"; then
    echo "$name: the reference build does not trap"; status=1
  elif diff -u "$work/reference/$name.out" "$work/$mode/$name.out" &&
       { [[ ! -e $work/combined/$name.out ]] || diff -u "$work/reference/$name.out" "$work/combined/$name.out"; }; then
    echo "$name: ok ($(grep -m1 'filc safety error' "$work/$mode/$name.out"))"
  else
    status=1
  fi
done
exit $status
