# Fixed preprocessed inputs for compile.py: small compression code, the Lua
# VM, and the large SQLite amalgamation. Keep preprocessing out of timings.
{
  flake ? builtins.getFlake (toString ../..),
  pkgs ? import flake.inputs.nixpkgs { system = "x86_64-linux"; },
  filcc ? flake.packages.x86_64-linux.filcc-staging,
}:
let
  sqlite = import ../nix/sqlite.nix { inherit pkgs filcc; };
in
pkgs.runCommand "nanofil-compile-inputs" { } ''
  mkdir $out lua bzip2
  tar -xf ${pkgs.lua5_4.src} -C lua --strip-components=1
  tar -xf ${pkgs.bzip2.src} -C bzip2 --strip-components=1
  cc=${filcc}/bin/clang
  $cc -E -O2 -U__SIZEOF_INT128__ -U__BITINT_MAXWIDTH__ \
    -D_FILE_OFFSET_BITS=64 bzip2/compress.c >$out/compress.i
  $cc -E -O2 -std=gnu99 -U__SIZEOF_INT128__ -U__BITINT_MAXWIDTH__ \
    -DLUA_USE_LINUX -DLUA_USE_JUMPTABLE=0 lua/src/lvm.c >$out/lvm.i
  $cc -E -O2 -U__SIZEOF_INT128__ -U__BITINT_MAXWIDTH__ \
    -DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION \
    -DSQLITE_ENABLE_FTS5 -DSQLITE_ENABLE_MATH_FUNCTIONS \
    -I${sqlite.amalgamation} ${sqlite.amalgamation}/sqlite3.c >$out/sqlite3.i
''
