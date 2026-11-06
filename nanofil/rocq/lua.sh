#!/usr/bin/env bash
# Lua's own functions as input for the Rocq model's gates (docs/rocq.md):
# rocq/tests/lua.c includes Lua's lctype.c, lobject.c and lstring.c from
# LUA_SRC (Lua 5.4.7's src/ directory), preprocessed by FILCC with the
# flags nix/lua.nix builds Lua with, as nix/nanofil-cc.nix does. Prints
# its IR, with its "// run:" lines as run facts, so that rocq/agree.sh
# and rocq/valid.sh take it as a .ir file.
#
#   FILCC=.../bin/clang lua.sh LUA_SRC >lua.ir
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
lua_src=$(cd "$1" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
"$FILCC" -O2 -std=gnu99 -DLUA_USE_LINUX -DLUA_USE_JUMPTABLE=0 -U__SIZEOF_INT128__ \
  -I"$lua_src" -E -o "$work/lua.i" "$here/tests/lua.c"
(cd "$here/../src" && ../bin/nanofil cc-ir "$work/lua.i" </dev/null)
awk '/^\/\/ run: \$/ { sub(/^\/\/ run: \$/, ""); fn = $1; $1 = ""
     sub(/^ +/, ""); gsub(/ +/, ", "); printf "run(\x27%s\x27, [%s]).\n", fn, $0 }' \
  "$here/tests/lua.c"
