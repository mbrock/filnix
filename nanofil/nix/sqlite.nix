# SQLite 3.51.2 (the amalgamation and its shell) built entirely by
# nanofil, single-threaded, with FTS5 and the math functions as nixpkgs
# enables them. A deterministic workload (tests/sqlite/workload.sql:
# DDL, inserts, indexes, joins, aggregates and windows, printf and
# floats, dates, JSON, FTS5, triggers, savepoints, the shell's output
# modes and a VACUUM) must print the same bytes and leave the same
# database file as a filcc-built sqlite3, plain and under FUGC_SCRIBBLE
# and FUGC_VERIFY, for nanofil's reference and its optimized
# configuration. sqlite3.c alone is 260,000 lines; nanofil compiles it in
# about 2.5 minutes and 3 GB, so each configuration builds one sqlite3.
{ pkgs, filcc }:
assert pkgs.sqlite.version == "3.51.2";
let
  flags = "-DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION -DSQLITE_ENABLE_FTS5 -DSQLITE_ENABLE_MATH_FUNCTIONS";
  workload = ../tests/sqlite/workload.sql;
  # The nixpkgs source is the canonical tree; generate the amalgamation
  # (sqlite3.c, sqlite3.h) and the single-file shell.c from it.
  amalgamation =
    pkgs.runCommandCC "sqlite-amalgamation-3.51.2"
      {
        src = pkgs.sqlite.src;
        nativeBuildInputs = [
          pkgs.unzip
          pkgs.tcl
        ];
      }
      ''
        unzip -q $src
        cd sqlite-src-*
        ./configure --disable-tcl >/dev/null
        make -j$NIX_BUILD_CORES sqlite3.c shell.c >/dev/null
        mkdir $out
        cp sqlite3.c sqlite3.h shell.c $out/
      '';
  reference = pkgs.runCommandCC "nanofil-sqlite-reference" { } ''
    mkdir $out
    ${filcc}/bin/clang -O1 ${flags} -I${amalgamation} -o $out/sqlite3 \
      ${amalgamation}/shell.c ${amalgamation}/sqlite3.c -lm
    $out/sqlite3 $out/workload.db <${workload} >$out/workload.out 2>&1
  '';
in
pkgs.runCommandCC "nanofil-sqlite"
  {
    passthru = { inherit amalgamation reference; };
  }
  ''
    cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
    cp ${amalgamation}/* .
    for opt in "" "-O --registers=local --checks=reuse"; do
      echo "== SQLite 3.51.2, nanofil $opt"
      rm -f *.o sqlite3 nanofil.log
      export NANOFIL_OPT=$opt NANOFIL_LOG=$PWD/nanofil.log NANOFIL_STACK_LIMIT=4000000000
      start=$SECONDS
      $cc -c ${flags} -I. sqlite3.c -o sqlite3.o
      $cc -c ${flags} -I. shell.c -o shell.o
      echo "compiled in $((SECONDS - start)) s"
      $cc -o sqlite3 shell.o sqlite3.o -lm
      # No object may come from clang.
      printf 'shell.o\nsqlite3.o\n' | diff -u - <(sort nanofil.log)
      for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
        rm -f workload.db
        env $env ./sqlite3 workload.db <${workload} >workload.out 2>&1
        diff -u ${reference}/workload.out workload.out
        cmp ${reference}/workload.db workload.db
        echo "sqlite3 matches filcc's output and database byte for byte ($env)"
      done
    done
    touch $out
  ''
