# The extracted Rocq validator as a gate on the compiler's -O products
# (rocq/scripts/gate.sh, docs/rocq.md): every checked module nanofil -O gives
# its backend, for the IR and C corpus (tests/, cproc, c-testsuite) and
# for each translation unit of GNU hello, zlib, Lua and SQLite, goes to
# the model's --module mode, which judges it as Validate.v's [valid]
# does, the validator Soundness.v's [valid_no_unchecked] is proved
# sound for. The check fails on any module the model rejects; modules
# with functions outside the model's subset are counted, not failed.
#
#   nix build -L .#checks.x86_64-linux.nanofil-rocq-gate
#
# The driver is rocq.nix's model.driver, which needs only Extract.v's
# import closure, 14 of the theories, each its own derivation; it does
# not wait for the rest of the model.
# The packages compile once each, in their own derivations, through
# nanofil-cc's terms mode, which takes the objects from filcc so the
# builds still link; only src/ and bin/ reach them.
{
  pkgs,
  filcc,
  driver,
}:
let
  inherit (pkgs) lib;
  nanofil = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../src
      ../bin
    ];
  };
  corpus = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../src
      ../bin
      ../tests
      ../rocq/scripts/gate.sh
    ];
  };
  sources = import ./corpus.nix { inherit pkgs; };
  cc = import ./nanofil-cc.nix {
    inherit pkgs filcc;
    src = nanofil;
    terms = true;
  };
  # terms NAME BUILD: run BUILD with CC=$cc, -O, and keep each
  # translation unit's checked module in $out.
  terms =
    name: build:
    pkgs.runCommandCC "nanofil-gate-terms-${name}" { } ''
      mkdir $out
      export NANOFIL_OPT=-O NANOFIL_TERMS=$out NANOFIL_LOG=$PWD/nanofil.log
      start=$SECONDS
      ${build}
      echo "@@nanofil-gate ${name}: $(ls $out | wc -l) modules in $((SECONDS - start)) s"
    '';
  packages = {
    hello = terms "hello" ''
      tar -xf ${pkgs.hello.src} --strip-components=1
      CC=${filcc}/bin/clang ./configure --disable-nls >/dev/null
      make -j$NIX_BUILD_CORES CC=${cc} >make.log 2>&1 || { tail -50 make.log; exit 1; }
    '';
    zlib = terms "zlib" ''
      tar -xf ${pkgs.zlib.src} --strip-components=1
      CC=${filcc}/bin/clang ./configure --static >/dev/null
      make -j$NIX_BUILD_CORES CC=${cc} libz.a example minigzip >make.log 2>&1 || { tail -50 make.log; exit 1; }
    '';
    lua = terms "lua" ''
      tar -xf ${pkgs.lua5_4.src} --strip-components=1
      make -C src -j$NIX_BUILD_CORES CC=${cc} SYSLIBS="-Wl,-E -ldl" \
        CFLAGS="-O2 -std=gnu99 -DLUA_USE_LINUX -DLUA_USE_JUMPTABLE=0" all >make.log 2>&1 ||
        { tail -50 make.log; exit 1; }
    '';
    sqlite =
      let
        sqlite = import ./sqlite.nix { inherit pkgs filcc; };
        flags = "-DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION -DSQLITE_ENABLE_FTS5 -DSQLITE_ENABLE_MATH_FUNCTIONS";
      in
      # Under -O sqlite3.c overflows the default 1 GB stack (docs/perf.md
      # item 20); start at nanofil-cc's retry limit instead of failing first.
      terms "sqlite" ''
        export NANOFIL_STACK_LIMIT=4000000000
        cp ${sqlite.amalgamation}/* .
        ${cc} -c ${flags} -I. sqlite3.c -o sqlite3.o &
        ${cc} -c ${flags} -I. shell.c -o shell.o
        wait $!
      '';
  };
  # judge NAME FILES: gate.sh on FILES, on every core; fails if the
  # model rejects any module, after printing the verdicts' summary.
  judge =
    name: files:
    pkgs.runCommandCC "nanofil-rocq-gate-${name}"
      {
        nativeBuildInputs = [
          pkgs.swi-prolog
          pkgs.python3
        ];
      }
      ''
        set -o pipefail
        cp -r ${corpus} nanofil
        chmod -R u+w nanofil
        cd nanofil
        patchShebangs bin tests rocq
        export FILCC=${filcc}/bin/clang MODEL=${driver}/bin/nanofil-model NANOFIL_JOBS=$NIX_BUILD_CORES
        bin/nanofil --save-state "$TMPDIR/nanofil.state"
        export NANOFIL_STATE=$TMPDIR/nanofil.state
        mkdir $out
        start=$SECONDS status=0
        tests/par.sh rocq/scripts/gate.sh ${files} >$out/log 2>&1 || status=1
        grep -h '^@@nanofil-gate ' $out/log >$out/verdicts || true
        awk '{ n[$2]++ } END { for (v in n) printf "${name} %s %d\n", v, n[v] }' $out/verdicts | sort >$out/summary
        cat $out/summary
        echo "@@nanofil-gate ${name} judged in $((SECONDS - start)) s"
        if [ $status != 0 ]; then
          grep -E '^@@nanofil-gate (invalid|error) ' $out/verdicts || true
          grep -E 'FAILED|failed' $out/log | head -40
          echo "nanofil-rocq-gate: the model rejects a module nanofil -O emits for ${name} (above)" >&2
          exit 1
        fi
      '';
  parts = {
    corpus = judge "corpus" ''
      tests/filc/*.ir tests/fixtures/*.ir tests/backend/*.ir tests/float/*.ir tests/c/*.c tests/c/prog/*.c \
        $(find ${sources.cproc}/test ${sources.c-testsuite}/tests/single-exec -name '*.c' | sort)'';
  }
  // lib.mapAttrs (name: p: judge name "${p}/*.terms") packages;
in
pkgs.runCommand "nanofil-rocq-gate"
  {
    passthru = { inherit driver packages parts; };
  }
  ''
    mkdir $out
    ${lib.concatMapStringsSep "\n" (
      n:
      "cat ${parts.${n}}/summary >>$out/summary; cat ${parts.${n}}/verdicts >>$out/verdicts"
    ) (builtins.attrNames parts)}
    cat $out/summary
  ''
