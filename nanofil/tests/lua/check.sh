#!/usr/bin/env bash
# Compare deterministic -e scripts, then run the unchanged official basic
# suite on both Lua binaries, plainly and under Fil-C GC stress. Official
# suite output includes clocks, memory counts and random seeds: assertions
# and its final success marker, not a misleading text diff, are its oracle.
# Usage: check.sh REFERENCE CANDIDATE OFFICIAL_TESTS_DIR OUTPUT_DIR
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
ref=$(realpath "$1")
candidate=$(realpath "$2")
official=$(realpath "$3")
mkdir -p "$4"
out=$(realpath "$4")
export LC_ALL=C
unset LUA_INIT LUA_INIT_5_4 LUA_PATH LUA_PATH_5_4 LUA_CPATH LUA_CPATH_5_4
unset FUGC_SCRIBBLE FUGC_VERIFY

for mode in plain gc; do
  stress=()
  if [ "$mode" = gc ]; then stress=(FUGC_SCRIBBLE=1 FUGC_VERIFY=1); fi
  for side in ref candidate; do
    if [ "$side" = ref ]; then lua=$ref; else lua=$candidate; fi
    dir="$out/$mode-$side"
    mkdir -p "$dir"
    for script in "$here"/*.lua; do
      name=$(basename "$script" .lua)
      if ! env "${stress[@]}" timeout "${LUA_TEST_TIMEOUT:-300}" "$lua" \
          "-e$(cat "$script")" >"$dir/$name.out" 2>"$dir/$name.err"; then
        cat "$dir/$name.out" "$dir/$name.err"
        echo "Lua -e $name failed ($mode $side)" >&2
        exit 1
      fi
    done
    mkdir "$dir/official"
    cp -R "$official"/. "$dir/official/"
    chmod -R u+w "$dir/official"
    # calls.lua's deep C recursion is also a frame-size regression test.
    # Both compilers must pass at the default Linux 8 MiB stack limit,
    # including GC stress and both nanofil optimization modes.
    if ! (ulimit -s 8192 && cd "$dir/official" && env "${stress[@]}" \
        timeout "${LUA_TEST_TIMEOUT:-300}" "$lua" -e '_U=true' all.lua) \
        >"$dir/official.out" 2>"$dir/official.err"; then
      cat "$dir/official.out" "$dir/official.err"
      echo "Lua official basic suite failed ($mode $side)" >&2
      exit 1
    fi
    if ! grep -q '^final OK !!!$' "$dir/official.out"; then
      cat "$dir/official.out" "$dir/official.err"
      echo "Lua official basic suite missing success marker ($mode $side)" >&2
      exit 1
    fi
    rm -rf "$dir/official"
    echo "Lua official basic suite: final OK ($mode $side)"
  done
  for script in "$here"/*.lua; do
    name=$(basename "$script" .lua)
    diff -u "$out/$mode-ref/$name.out" "$out/$mode-candidate/$name.out"
    diff -u "$out/$mode-ref/$name.err" "$out/$mode-candidate/$name.err"
    echo "Lua -e $name: byte-identical stdout/stderr ($mode)"
  done
done
