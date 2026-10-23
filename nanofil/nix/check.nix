# nanofil: unit tests, then the fixtures and a seeded random corpus run
# through the interpreter, qbe and nanofil's own backend. nanofil alone
# must also get the qbe-bugs repros right. Fil-C modules (tests/filc) are
# linked with clang-built Fil-C code and run natively; the GC test also
# runs with FUGC_SCRIBBLE and FUGC_VERIFY, which a missed root or store
# barrier needs to show up. C files (tests/c) are compiled by nanofil and
# by clang and both run against the interpreter; tests/c/reject must be
# refused with the expected messages. Whole programs (tests/c/prog) are
# built by nanofil and by clang and must print and exit the same, also
# under FUGC_SCRIBBLE and FUGC_VERIFY. Then everything runs again with
# the M5 middle end (-O), validated run by run by the interpreter.
# Everything runs on SWI-Prolog; a short last step repeats the unit tests,
# the C difftests and the programs on Trealla, the other supported host.
{ pkgs, filcc }:
let
  trealla = import ./trealla.nix { inherit pkgs; };
  qbe = import ./qbe.nix { inherit pkgs; };
  corpus = import ./corpus.nix { inherit pkgs; };
in
pkgs.runCommandCC "nanofil-check"
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      trealla
      qbe
      pkgs.python3
    ];
  }
  ''
    # step LABEL CMD...: run CMD, printing when it starts and how long it
    # took as soon as it ends (watch with nix build -L); the table at the
    # end sums it up.
    check_t0=$SECONDS
    step() {
      local label=$1 t0=$SECONDS
      shift
      echo ">>> [$((SECONDS - check_t0))s] start: $label"
      "$@"
      echo "<<< [$((SECONDS - check_t0))s] done in $((SECONDS - t0))s: $label"
      printf '%5ds  %s\n' $((SECONDS - t0)) "$label" >>"$TMPDIR/timings"
    }
    cp -r ${../.} nanofil
    chmod -R u+w nanofil
    cd nanofil
    patchShebangs tests bin
    step unit bash -c '(cd src && ../bin/nanofil --script ../tests/unit.pl </dev/null) | tee unit.log'
    grep -q 'tests ok$' unit.log
    # M9 IR/interpreter contract, independent of the backend workstream.
    # Integer-bit wrappers preserve NaN payloads and negative zero.
    step "difftest float SSE2" env CC=$CC VARIANTS="original printed" tests/difftest.sh tests/float/*.ssa
    python3 -I tests/gen.py 1 200 > gen1.ssa
    step "difftest fixtures+gen1" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ssa gen1.ssa
    step "difftest qbe-bugs" env CC=$CC VARIANTS=nanofil tests/par.sh tests/difftest.sh tests/qbe-bugs/*.ssa
    export FILCC=${filcc}/bin/clang
    step pptest tests/pptest.sh
    step "difftest filc/*.ssa" tests/par.sh tests/difftest.sh tests/filc/basic.ssa tests/filc/globals.ssa tests/filc/tuples.ssa tests/filc/copy.ssa
    step "run-c interop gc" tests/par.sh tests/filc/run-c.sh interop gc
    step "variadic gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh variadic
    step "difftest c/*.c" tests/par.sh tests/difftest.sh tests/c/*.c
    step reject tests/reject.sh
    step progtest tests/par.sh tests/progtest.sh tests/c/prog/*.c
    # c-testsuite/00200 (1557 blocks) is the slowest compile (docs/m5.md).
    step corpus env COMPILE_TIMEOUT=60 python3 -I tests/corpus.py ${corpus.cproc} ${corpus.c-testsuite}
    step "progtest gc-stress" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    step "run-c gc gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh gc
    # M5: the same suites with the middle end on. difftest -O also runs
    # every run line on the unoptimized module and checks that each result
    # refines it; unit.pl checks promotion, copy removal, exact pointer
    # identity and bounded symbolic before/after equivalence.
    python3 -I tests/bigfn.py 1 300 > big1.c
    export NANOFIL_OPT=-O
    step "-O difftest float SSE2" env CC=$CC VARIANTS="original printed" tests/difftest.sh tests/float/*.ssa
    step "-O difftest fixtures+gen1" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ssa gen1.ssa
    step "-O difftest qbe-bugs" env CC=$CC VARIANTS=nanofil tests/par.sh tests/difftest.sh tests/qbe-bugs/*.ssa
    step "-O difftest filc, c, big1" tests/par.sh tests/difftest.sh tests/filc/basic.ssa tests/filc/globals.ssa tests/filc/tuples.ssa tests/filc/copy.ssa tests/c/*.c big1.c
    step "-O run-c interop gc" tests/par.sh tests/filc/run-c.sh interop gc
    step "-O variadic gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh variadic
    step "-O progtest" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    step "-O progtest gc-stress" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    step "-O run-c gc gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh gc
    unset NANOFIL_OPT
    # The functional, versioned-fact and incremental analyses must agree.
    python3 -I tests/bigfn.py 2 100 > big2.c
    step bench-cfg bash -c '(cd src && ../bin/nanofil --script ../tests/bench-cfg.pl ../big2.c </dev/null)'
    export NANOFIL_HOST=trealla
    step "trealla: unit, difftest c/*.c, progtest" bash -ec '
      (cd src && ../bin/nanofil --script ../tests/unit.pl </dev/null) | tee unit.log
      grep -q "tests ok$" unit.log
      VARIANTS="original printed" tests/difftest.sh tests/float/*.ssa
      NANOFIL_OPT=-O VARIANTS="original printed" tests/difftest.sh tests/float/*.ssa
      tests/par.sh tests/difftest.sh tests/c/*.c
      tests/par.sh tests/progtest.sh tests/c/prog/*.c'
    unset NANOFIL_HOST
    echo "== nanofil check timings"
    cat "$TMPDIR/timings"
    touch $out
  ''
