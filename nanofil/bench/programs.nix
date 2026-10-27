# The benchmark's programs: for a C compiler `cc` (a path), a
# derivation per program with its executable at the top of $out.
# NANOFIL_OPT selects nanofil's mode when cc is nanofil-cc.
{ pkgs, filcc }:
let
  luaFlags = "-O2 -std=gnu99 -DLUA_USE_LINUX -DLUA_USE_JUMPTABLE=0";
  sqliteFlags = "-O2 -DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION -DSQLITE_ENABLE_FTS5 -DSQLITE_ENABLE_MATH_FUNCTIONS";
  progs = {
    zlib = {
      src = pkgs.zlib.src;
      exe = "minigzip";
      build = cc: ''
        mkdir p && tar -xf $src -C p --strip-components=1
        (cd p && CC=${filcc}/bin/clang ./configure --static >/dev/null)
        make -C p -j$NIX_BUILD_CORES CC=${cc} libz.a minigzip >/dev/null
        cp p/minigzip $out/'';
    };
    lua = {
      src = pkgs.lua5_4.src;
      exe = "lua";
      build = cc: ''
        mkdir p && tar -xf $src -C p --strip-components=1
        make -C p/src -j$NIX_BUILD_CORES CC=${cc} CFLAGS="${luaFlags}" SYSLIBS="-Wl,-E -ldl" lua >/dev/null
        cp p/src/lua $out/'';
    };
    bzip2 = {
      src = pkgs.bzip2.src;
      exe = "bzip2";
      build = cc: ''
        mkdir p && tar -xf $src -C p --strip-components=1
        make -C p -j$NIX_BUILD_CORES CC=${cc} bzip2 >/dev/null
        cp p/bzip2 $out/'';
    };
    lz4 = {
      src = pkgs.lz4.src;
      exe = "lz4";
      build = cc: ''
        cp -r $src p && chmod -R u+w p
        make -C p/programs -j$NIX_BUILD_CORES CC=${cc} lz4 >/dev/null
        cp p/programs/lz4 $out/'';
    };
    # The amalgamation nix/sqlite.nix generates; sqlite3.c needs about 3 GB
    # of Prolog stack in nanofil (NANOFIL_STACK_LIMIT).
    sqlite = {
      src = (import ../nix/sqlite.nix { inherit pkgs filcc; }).amalgamation;
      exe = "sqlite3";
      build = cc: ''
        export NANOFIL_STACK_LIMIT=4000000000
        ${cc} ${sqliteFlags} -I$src -c $src/sqlite3.c -o sqlite3.o &
        ${cc} ${sqliteFlags} -I$src -c $src/shell.c -o shell.o
        wait $!
        ${cc} -o $out/sqlite3 shell.o sqlite3.o -lm'';
    };
  };
in
{
  inherit progs;
  # build NAME LABEL CC OPT [EXTRA]: program NAME built by CC with
  # NANOFIL_OPT=OPT; EXTRA runs after the build, in the build directory.
  build =
    name: label: cc: opt: extra:
    pkgs.runCommandCC "nanofil-bench-${name}-${label}"
      { src = progs.${name}.src; }
      ''
        mkdir $out
        export NANOFIL_OPT="${opt}"
        ${progs.${name}.build cc}
        ${extra}
      '';
}
