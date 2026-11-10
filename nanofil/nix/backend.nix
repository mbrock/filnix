# The Gallina backend (rocq/backend, docs/gallina-backend.md): the
# compiler's middle and back end in Gallina, extracted to OCaml and
# held to the Prolog compiler's output byte for byte. Off the quick
# Rocq gate: nothing in the model imports it.
#
#   nix build -L .#checks.x86_64-linux.nanofil-backend
#   nix build -L .#checks.x86_64-linux.nanofil-backend-full
#
# It compiles the backend and the model files it imports (theories;
# not the model's proofs, so this does not wait for them), printing
# each file's time, extracts and links bin/nanofil-backend, and runs
# the gates of the milestones reached so far. M1: the extracted
# printer prints asm.pl's text from the lines the Prolog compiler
# emits (rocq/backend/tests/asm.sh), on the Fil-C IR fixtures and
# seven C programs that between them reach every line form; full=true
# takes the whole corpus, with and without -O. M2: the extracted ABI
# plans are the terms filc_abi.pl prints (rocq/backend/tests/abi.sh),
# on the same files and six more C programs that reach the plan forms
# the others lack; full=true takes the whole corpus. NFB: Nfb.v's
# writer writes the words nfb.pl writes and its reader reads them back
# (rocq/backend/tests/nfb.sh, docs/nfb.md), on the same files; full=true
# takes the whole corpus, with and without -O. M3: the lines the
# backend gives each function's plan, each data item, alias and weak
# thunk are the reference emission's, and without -O the whole
# module's text is `nanofil compile`'s wherever every function is in
# the subset (rocq/backend/tests/emit.sh), on the same files and the
# fixtures of rocq/backend/tests/edge, which reach the arms the corpus
# does not; full=true takes the whole corpus, with and without -O,
# and then every translation unit of zlib, GNU hello and Lua as
# nanofil-cc preprocesses it (nanofil-cc.nix, hello.nix, lua.nix),
# where the whole text must be `nanofil cc`'s. M4: Pizlonate.v makes
# of a module the term pizlonate.pl makes of it
# (rocq/backend/tests/pizlonate.sh), on the same files and the
# fixtures of rocq/backend/tests/pizlonate; full=true takes the whole
# corpus, with and without -O, and the translation units. M5b:
# Promote.v makes of a module the term promote.pl makes of it, and
# Copy.v of that the term copy.pl makes of it
# (rocq/backend/tests/promote.sh), on the same files and the
# fixtures of rocq/backend/tests/promote; full=true takes the whole
# corpus. And
# `nanofil-backend compile`, which reads IR text itself, prints what
# `nanofil compile` prints and refuses what it refuses
# (rocq/backend/tests/compile.sh), on the same files and the fixtures
# of rocq/backend/tests/compile; full=true takes the whole corpus and
# the translation units; the files it does not take are exactly
# those rocq/backend/tests/compile/none.txt names. And
# `nanofil-backend compile-promoted`, which promotes, propagates
# copies and selects branches, prints what `nanofil compile-promoted`
# prints, on the same files and the fixtures of
# rocq/backend/tests/promote. Its reader,
# IrText.v, reads the module Prolog reads and nothing where Prolog
# throws (rocq/backend/tests/read.sh), on the IR fixtures and on a
# thousand adversarial texts, those also cut into pieces of one and
# of seven bytes. Then parse.sh reads every backend
# sentence back (web/rocq).
{
  pkgs,
  filcc,
  full ? false,
}:
let
  rocq = pkgs.rocqPackages;
  ocamlPackages = rocq.rocq-core.ocamlPackages;
  src = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../src
      ../bin
      ../tests
      ../rocq/theories
      ../rocq/backend
      ../web/rocq/rocq_syntax.pl
      ../web/rocq/tests/parse.sh
      ../web/rocq/tests/reprint.pl
    ];
  };
  quick = "tests/filc/*.ir tests/c/ldouble.c tests/c/prog/address-difference.c tests/c/prog/alias.c tests/c/prog/asm-fixed.c tests/c/prog/constructor.c tests/c/prog/source-bytes.c tests/c/prog/thread-local.c";
  quickAbi = "${quick} tests/c/fstructs.c tests/c/variadic.c tests/c/prog/structs.c tests/c/prog/memcpy-small.c tests/c/prog/weak-symbols.c tests/c/prog/byval.c";
  corpus = "tests/filc/*.ir tests/c/*.c tests/c/prog/*.c";
  edge = "rocq/backend/tests/edge/*.ir";
  pizlonate = "rocq/backend/tests/pizlonate/*.ir";
  compile = "${edge} ${pizlonate} rocq/backend/tests/compile/*.ir";
  promote = "rocq/backend/tests/promote/*.ir";
  regs = "rocq/backend/tests/regs/*.ir";
  # zlib, GNU hello and Lua, built through nanofil-cc as their own
  # checks build them, keeping each preprocessed translation unit.
  # None of their flags makes nanofil-cc set NANOFIL_STD or
  # NANOFIL_COMMON, which emit.sh would not know of.
  cc = import ./nanofil-cc.nix { inherit pkgs filcc; };
  packages = ''
    mkdir units zlib hello lua
    export NANOFIL_KEEP_I=$PWD/units
    tar -xf ${pkgs.zlib.src} -C zlib --strip-components=1
    (cd zlib && CC=${filcc}/bin/clang ./configure --static >configure.log &&
      make -j$NIX_BUILD_CORES CC=${cc} libz.a example minigzip >make.log 2>&1) ||
      { tail -50 zlib/make.log; exit 1; }
    tar -xf ${pkgs.hello.src} -C hello --strip-components=1
    (cd hello && CC=${filcc}/bin/clang ./configure --disable-nls >configure.log 2>&1 &&
      make -j$NIX_BUILD_CORES CC=${cc} >make.log 2>&1) ||
      { tail -50 hello/make.log; exit 1; }
    tar -xf ${pkgs.lua5_4.src} -C lua --strip-components=1
    make -C lua/src -j$NIX_BUILD_CORES CC=${cc} SYSLIBS="-Wl,-E -ldl" \
      CFLAGS="-O2 -std=gnu99 -DLUA_USE_LINUX -DLUA_USE_JUMPTABLE=0" all >lua/make.log 2>&1 ||
      { tail -50 lua/make.log; exit 1; }
    unset NANOFIL_KEEP_I
    echo "kept $(ls units | wc -l) translation units of zlib, hello and Lua"
    tests/par.sh rocq/backend/tests/emit.sh units/*.i | tee emit-packages.log
    tests/par.sh rocq/backend/tests/pizlonate.sh units/*.i | tee pizlonate-packages.log
    tests/par.sh rocq/backend/tests/compile.sh units/*.i | tee compile-packages.log
    COMMAND=compile-promoted tests/par.sh rocq/backend/tests/compile.sh units/*.i | tee compile-promoted-packages.log
    tests/par.sh rocq/backend/tests/regs.sh units/*.i | tee regs-packages.log
  '';
in
pkgs.runCommandCC (if full then "nanofil-backend-full" else "nanofil-backend")
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      pkgs.python3
      rocq.rocq-core
      rocq.stdlib
      ocamlPackages.ocaml
      ocamlPackages.findlib
    ];
    buildInputs = [ ocamlPackages.zarith ];
  }
  (
    ''
      set -o pipefail
      cp -r ${src} nanofil
      chmod -R u+w nanofil
      cd nanofil
      patchShebangs bin tests rocq/backend
      make -C rocq/backend -j"$NIX_BUILD_CORES" | tee timings.log
      export FILCC=${filcc}/bin/clang NANOFIL_JOBS=$NIX_BUILD_CORES
      bin/nanofil --save-state "$TMPDIR/nanofil.state"
      export NANOFIL_STATE=$TMPDIR/nanofil.state
    ''
    + (
      if full then
        ''
          tests/par.sh rocq/backend/tests/asm.sh ${corpus} | tee asm.log
          NANOFIL_OPT=-O tests/par.sh rocq/backend/tests/asm.sh ${corpus} | tee asm-O.log
          tests/par.sh rocq/backend/tests/abi.sh ${corpus} | tee abi.log
          tests/par.sh rocq/backend/tests/nfb.sh ${corpus} rocq/backend/tests/nfb/*.ir | tee nfb.log
          NANOFIL_OPT=-O tests/par.sh rocq/backend/tests/nfb.sh ${corpus} rocq/backend/tests/nfb/*.ir | tee nfb-O.log
          tests/par.sh rocq/backend/tests/nfb-compile.sh tests/filc/*.ir | tee nfb-compile.log
          tests/par.sh rocq/backend/tests/emit.sh ${corpus} ${edge} | tee emit.log
          NANOFIL_OPT=-O tests/par.sh rocq/backend/tests/emit.sh ${corpus} ${edge} | tee emit-O.log
          tests/par.sh rocq/backend/tests/pizlonate.sh ${corpus} ${pizlonate} | tee pizlonate.log
          NANOFIL_OPT=-O tests/par.sh rocq/backend/tests/pizlonate.sh ${corpus} ${pizlonate} | tee pizlonate-O.log
          tests/par.sh rocq/backend/tests/promote.sh ${corpus} ${compile} ${promote} | tee promote.log
          tests/par.sh rocq/backend/tests/compile.sh ${corpus} ${compile} | tee compile.log
          COMMAND=compile-promoted tests/par.sh rocq/backend/tests/compile.sh ${corpus} ${compile} ${promote} | tee compile-promoted.log
          REGS_GC=1 tests/par.sh rocq/backend/tests/regs.sh ${corpus} ${compile} ${promote} ${regs} | tee regs.log
        ''
        + packages
      else
        ''
          tests/par.sh rocq/backend/tests/asm.sh ${quick} | tee asm.log
          tests/par.sh rocq/backend/tests/abi.sh ${quickAbi} | tee abi.log
          tests/par.sh rocq/backend/tests/nfb.sh ${quickAbi} rocq/backend/tests/nfb/*.ir | tee nfb.log
          tests/par.sh rocq/backend/tests/nfb-compile.sh tests/filc/*.ir | tee nfb-compile.log
          tests/par.sh rocq/backend/tests/emit.sh ${quickAbi} ${edge} | tee emit.log
          tests/par.sh rocq/backend/tests/pizlonate.sh ${quickAbi} ${pizlonate} | tee pizlonate.log
          tests/par.sh rocq/backend/tests/promote.sh ${quickAbi} ${compile} ${promote} | tee promote.log
          tests/par.sh rocq/backend/tests/compile.sh ${quickAbi} ${compile} | tee compile.log
          COMMAND=compile-promoted tests/par.sh rocq/backend/tests/compile.sh ${quickAbi} ${compile} ${promote} | tee compile-promoted.log
          REGS_GC=1 tests/par.sh rocq/backend/tests/regs.sh ${quickAbi} ${compile} ${promote} ${regs} | tee regs.log
        ''
    )
    + ''
      python3 tests/watch.py --label "read cases" -- rocq/backend/tests/read.sh --cases | tee read-cases.log
      for piece in 1 7; do
        NANOFIL_BACKEND_PIECE=$piece python3 tests/watch.py --label "read cases, pieces of $piece" -- \
          rocq/backend/tests/read.sh --cases | tee read-cases-$piece.log
      done
      python3 tests/watch.py --label "read fixtures" -- rocq/backend/tests/read.sh tests/filc/*.ir ${compile} | tee read.log
      python3 tests/watch.py --label "backend parse/typecheck" -- bash web/rocq/tests/parse.sh rocq/backend/*.v
      mkdir -p $out/bin
      cp rocq/backend/nanofil-backend $out/bin/
      cp timings.log asm*.log abi.log nfb*.log emit*.log pizlonate*.log promote.log compile*.log regs*.log read*.log $out/
    ''
  )
