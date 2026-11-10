#!/usr/bin/env bash
# Behavioral gate for the Gallina register-allocated compiler
# (docs/gallina-backend.md, M7):
#   BACKEND=.../nanofil-backend [REGS_GC=1] regs.sh FILE...
#
# For each IR, C or preprocessed .i file:
# - refusal and outside-subset status must agree with
#   `nanofil compile-promoted` and compile/none.txt;
# - every taken module must compile with `compile-allocated`, assemble
#   cleanly with GNU as, and pass behavioral execution against the
#   oracle where runnable:
#   * tests/c/prog/*.c whole programs vs filcc;
#   * tests/filc/*.ir with .expected/.c companions (run-c);
#   * IR and C files with run(...) difftest facts vs the interpreter.
# With REGS_GC=1, runnable Fil-C binaries also run under
# FUGC_SCRIBBLE=1 FUGC_VERIFY=1.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nanofil_dir=$(cd "$here/../../.." && pwd)
src="$nanofil_dir/src"
nanofil="$nanofil_dir/bin/nanofil"
backend=${BACKEND:-$here/../nanofil-backend}
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

run_difftest_bin() {
  local exe=$1 n=$2 out=$3
  shift 3
  : >"$out"
  for ((i = 0; i < n; i++)); do
    if bash -c '"$@" >"$0.out" 2>"$0.err"; exit $?' "$work/r" "$@" "$exe" "$i" 2>/dev/null; then
      cat "$work/r.out" >>"$out"
    elif grep -q 'filc safety error' "$work/r.err"; then
      echo "$(cat "$work/r.out")trap" >>"$out"
    else
      echo "$(cat "$work/r.out")crash: $(head -c 200 "$work/r.err" | tr '\n' ' ')" >>"$out"
    fi
  done
}

status=0
for f in "$@"; do
  t0=$SECONDS
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  echo "@@nanofil-backend $(date -u +%FT%TZ) start regs file=$f"
  d="$work/case"
  rm -rf "$d" && mkdir -p "$d"

  case $f in
    *.i) name=$(basename "$f" | sed -E 's/^[0-9a-f]{6,8}-//') ;;
    *) name=$(basename "$(dirname "$f")")/$(basename "$f") ;;
  esac
  listed=
  if grep -qxF "$name" "$here/compile/none.txt"; then listed=1; fi

  ir=$f
  if [[ $f == *.c || $f == *.i ]]; then
    ir="$d/module.ir"
    if ! (cd "$src" && "$nanofil" cc-ir "$f" </dev/null) >"$ir" 2>"$d/err"; then
      echo "skip $f: $(head -c 100 "$d/err" | head -1)"
      continue
    fi
  fi

  theirs=0 ours=0
  (cd "$src" && "$nanofil" compile-promoted "$ir" </dev/null) >"$d/theirs.s" 2>"$d/their-err" || theirs=$?
  "$backend" compile-allocated "$ir" >"$d/ours.s" 2>"$d/our-err" || ours=$?
  why=$(tr -s ' \n' ' ' <"$d/our-err" | head -c 200)

  if [ "$theirs" != 0 ]; then
    if [ "$ours" = 0 ]; then
      echo "DIFFER $f: compile-allocated succeeded, and nanofil refuses"
      status=1
    else
      echo "refused $f: $why"
    fi
    continue
  elif [ "$ours" = 3 ]; then
    if [ -n "$listed" ]; then
      echo "none $f: $why"
    else
      echo "DIFFER $f: not taken, and compile/none.txt does not name $name: $why"
      status=1
    fi
    continue
  elif [ "$ours" != 0 ]; then
    echo "DIFFER $f: exit $ours, and nanofil compiles: $why"
    status=1
    continue
  elif [ -n "$listed" ]; then
    echo "DIFFER $f: taken, and compile/none.txt names $name"
    status=1
    continue
  fi

  # Every module whose reference assembly GNU as accepts must assemble cleanly.
  if as -o "$d/theirs.o" "$d/theirs.s" 2>/dev/null; then
    if ! as -o "$d/ours.o" "$d/ours.s" 2>"$d/as-err"; then
      echo "DIFFER $f: as failed: $(head -c 240 "$d/as-err")"
      status=1
      continue
    fi
  else
    echo "ok $f: $(wc -l <"$d/ours.s") lines (non-as symbol fixture)"
    echo "@@nanofil-backend $(date -u +%FT%TZ) done regs file=$f seconds=$((SECONDS - t0))"
    continue
  fi

  ran="assembled"
  stem="${f%.*}"
  if [[ $f == *.ir && -f "$stem.c" && -f "$stem.expected" ]]; then
    extra=()
    if [[ -f "$stem.s" ]]; then
      as -o "$d/native.o" "$stem.s"
      extra=("$d/native.o")
    fi
    "$filcc" -O1 -o "$d/runc" "$stem.c" "$d/ours.o" "${extra[@]}"
    n=$(wc -l <"$stem.expected")
    run_difftest_bin "$d/runc" "$n" "$d/actual.txt"
    if ! diff -u "$stem.expected" "$d/actual.txt" >"$d/diff"; then
      echo "DIFFER $f (run-c):"; head -n 30 "$d/diff"; status=1; continue
    fi
    if [ -n "${REGS_GC:-}" ]; then
      run_difftest_bin "$d/runc" "$n" "$d/actual-gc.txt" env FUGC_SCRIBBLE=1 FUGC_VERIFY=1
      if ! diff -u "$stem.expected" "$d/actual-gc.txt" >"$d/diff"; then
        echo "DIFFER $f (run-c gc):"; head -n 30 "$d/diff"; status=1; continue
      fi
    fi
    ran="run-c($n)"
  elif [[ "$name" == prog/*.c ]]; then
    # Whole program vs clang.
    if ! grep -qE '^// (nanofil-link|cflags):' "$f"; then
      ropt=$(sed -n 's|^// reference-opt: ||p' "$f"); ropt=${ropt:--O1}
      link_rel=$(sed -n 's|^// link: ||p' "$f")
      read -r -a pargs <<<"$(sed -n 's|^// args: ||p' "$f")"
      libs=()
      if [ -n "$link_rel" ]; then
        "$filcc" -O1 -w -c -o "$d/lib.o" "$(dirname "$f")/$link_rel"
        libs=("$d/lib.o")
      fi
      "$filcc" "$ropt" -w -o "$d/clang" "$f" "${libs[@]}" -lm
      if grep -q '^// link-first' "$f"; then
        "$filcc" -o "$d/alloc" "${libs[@]}" "$d/ours.o" -lm
      else
        "$filcc" -o "$d/alloc" "$d/ours.o" "${libs[@]}" -lm
      fi
      for which in clang alloc; do
        mkdir -p "$d/cwd-$which"
        set +e
        (cd "$d/cwd-$which" && bash -c '"$@" >"$0.out" 2>"$0.err"; exit $?' "$d/$which" timeout 10 "$d/$which" "${pargs[@]}" </dev/null) 2>/dev/null
        rc=$?
        set -e
        if grep -q 'filc safety error' "$d/$which.err"; then
          echo trap >"$d/$which.err"
          rc="trap"
        fi
        echo "exit $rc" >"$d/$which.st"
      done
      exp_out="$d/clang.out"
      if [[ -f "$f.nanofil" ]]; then exp_out="$f.nanofil"; fi
      if ! diff -u "$exp_out" "$d/alloc.out" || ! diff -u "$d/clang.err" "$d/alloc.err" || ! diff -u "$d/clang.st" "$d/alloc.st"; then
        echo "DIFFER $f (prog)"
        status=1; continue
      fi
      ran="prog"
    fi
  else
    dt_ir="$ir"
    if [[ $f == *.c ]] && grep -q '^// run: \$' "$f"; then
      dt_ir="$d/dt.ir"
      cp "$ir" "$dt_ir"
      awk '/^\/\/ run: \$/ { sub(/^\/\/ run: \$/, ""); fn = $1; $1 = ""
           sub(/^ +/, ""); gsub(/ +/, ", "); printf "run(\x27%s\x27, [%s]).\n", fn, $0 }' "$f" >>"$dt_ir"
    fi
    if grep -q '^run(' "$dt_ir" 2>/dev/null; then
      mkdir -p "$d/dt"
      (cd "$src" && "$nanofil" difftest "$dt_ir" "$d/dt" </dev/null) >/dev/null
      if [ "$(cat "$d/dt/mode")" = filc ]; then
        "$filcc" -O1 -fno-pie -no-pie -o "$d/alloc" "$d/dt/harness.c" "$d/ours.o"
        n=$(wc -l <"$d/dt/expected.txt")
        run_difftest_bin "$d/alloc" "$n" "$d/actual.txt"
        if ! diff -u "$d/dt/expected.txt" "$d/actual.txt" >"$d/diff"; then
          echo "DIFFER $f (difftest):"; head -n 30 "$d/diff"; status=1; continue
        fi
        if [ -n "${REGS_GC:-}" ]; then
          run_difftest_bin "$d/alloc" "$n" "$d/actual-gc.txt" env FUGC_SCRIBBLE=1 FUGC_VERIFY=1
          if ! diff -u "$d/dt/expected.txt" "$d/actual-gc.txt" >"$d/diff"; then
            echo "DIFFER $f (difftest gc):"; head -n 30 "$d/diff"; status=1; continue
          fi
        fi
        ran="difftest($n)"
      fi
    fi
  fi

  echo "ok $f: $(wc -l <"$d/ours.s") lines ($ran)"
  echo "@@nanofil-backend $(date -u +%FT%TZ) done regs file=$f seconds=$((SECONDS - t0))"
done
exit $status
