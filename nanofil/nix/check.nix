# nanofil: unit tests, then the IR fixtures, the backend regressions and
# a seeded random corpus run through the interpreter and nanofil's own
# backend, which must agree. Fil-C modules (tests/filc) are
# linked with clang-built Fil-C code and run natively; the GC test also
# runs with FUGC_SCRIBBLE and FUGC_VERIFY, which a missed root or store
# barrier needs to show up. C files (tests/c) are compiled by nanofil and
# by clang and both run against the interpreter; tests/c/reject must be
# refused with the expected messages. Whole programs (tests/c/prog) are
# built by nanofil and by clang and must print and exit the same, also
# under FUGC_SCRIBBLE and FUGC_VERIFY. Then everything runs again with
# the M5 middle end (-O), validated run by run by the interpreter.
# Everything runs on SWI-Prolog. Trealla, the other host, is paused
# (October 2026): with withTrealla = true a last step repeats the unit
# tests, the C difftests and the programs on it, and checks that it
# generates the same random corpus.
{
  pkgs,
  filcc,
  withTrealla ? false,
}:
let
  trealla = import ./trealla.nix { inherit pkgs; };
  corpus = import ./corpus.nix { inherit pkgs; };
in
pkgs.runCommandCC "nanofil-check"
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      pkgs.python3
    ]
    ++ pkgs.lib.optional withTrealla trealla;
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
    # Commands run from a saved state (bin/nanofil); scripts still load
    # src/, so both paths are tested.
    bin/nanofil --save-state "$TMPDIR/nanofil.state"
    export NANOFIL_STATE=$TMPDIR/nanofil.state
    step unit bash -c '(cd src && ../bin/nanofil --script ../tests/unit.pl </dev/null) | tee unit.log'
    grep -q 'tests ok$' unit.log
    # M9 interpreter against nanofil's SSE2 backend.
    # Integer-bit wrappers preserve NaN payloads and negative zero.
    step "difftest float SSE2" env CC=$CC tests/difftest.sh tests/float/*.ir
    (cd src && ../bin/nanofil --script ../tests/gen.pl 1 200 </dev/null) > gen1.ir
    step "difftest fixtures+gen1" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir
    step "difftest backend" env CC=$CC tests/par.sh tests/difftest.sh tests/backend/*.ir
    export FILCC=${filcc}/bin/clang
    step pptest tests/pptest.sh
    step "difftest filc/*.ir" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir
    step "run-c interop gc float" tests/par.sh tests/filc/run-c.sh interop gc float
    step "variadic+float gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh variadic float
    step "setjmp gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh setjmp
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
    step "-O difftest float SSE2" env CC=$CC tests/difftest.sh tests/float/*.ir
    step "-O difftest fixtures+gen1" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir
    step "-O difftest backend" env CC=$CC tests/par.sh tests/difftest.sh tests/backend/*.ir
    step "-O difftest filc, c, big1" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/c/*.c big1.c
    step "-O run-c interop gc float" tests/par.sh tests/filc/run-c.sh interop gc float
    step "-O variadic+float gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh variadic float
    step "-O setjmp gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh setjmp
    step "-O progtest" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    step "-O progtest gc-stress" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    step "-O run-c gc gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh gc
    unset NANOFIL_OPT
    # The functional, versioned-fact and incremental analyses must agree.
    python3 -I tests/bigfn.py 2 100 > big2.c
    step bench-cfg bash -c '(cd src && ../bin/nanofil --script ../tests/bench-cfg.pl ../big2.c </dev/null)'
    ${pkgs.lib.optionalString withTrealla ''
      export NANOFIL_HOST=trealla
      step "trealla: unit, gen1, difftest c/*.c, progtest" bash -ec '
        (cd src && ../bin/nanofil --script ../tests/unit.pl </dev/null) | tee unit.log
        grep -q "tests ok$" unit.log
        (cd src && ../bin/nanofil --script ../tests/gen.pl 1 200 </dev/null) | cmp - gen1.ir
        tests/difftest.sh tests/float/*.ir
        NANOFIL_OPT=-O tests/difftest.sh tests/float/*.ir
        tests/par.sh tests/difftest.sh tests/c/*.c
        tests/difftest.sh tests/fixtures/float.ir
        tests/filc/run-c.sh float
        RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh setjmp
        NANOFIL_OPT=-O RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh setjmp
        RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/progtest.sh tests/c/prog/setjmp.c tests/c/prog/setjmp-expired.c
        NANOFIL_OPT=-O RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/progtest.sh tests/c/prog/setjmp.c tests/c/prog/setjmp-expired.c
        tests/par.sh tests/progtest.sh tests/c/prog/*.c'
    ''}
    unset NANOFIL_HOST
    echo "== nanofil check timings"
    cat "$TMPDIR/timings"
    touch $out
  ''
