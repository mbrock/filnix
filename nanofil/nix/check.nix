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
      pkgs.gdb
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
    # Above the interactive 20 s: a check must not time out on a loaded
    # builder (unused-intrinsics.c took 22 s beside two CPython builds).
    export COMPILE_TIMEOUT=60
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
    # The guide's example outputs (docs/guide.md, README.md) are what the
    # compiler now produces.
    step guide tests/guide.sh --check
    step "difftest filc/*.ir" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/asm-fixed-runs.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/guard-span.ir tests/filc/branches.ir
    step "run-c interop gc float" tests/par.sh tests/filc/run-c.sh interop gc float asm-fixed
    step "variadic+float gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh variadic float
    step "setjmp gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh setjmp
    step "pointer+exception gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh pointer-effects lower-donor exceptions reuse-gc
    step "actual ensure-aux exits" tests/filc/trace-pointer-effects.sh
    step "difftest c/*.c" tests/par.sh tests/difftest.sh tests/c/*.c
    step reject tests/reject.sh
    # const_eval, the IR and clang on generated integer expressions (docs/arith.md).
    step "arith slice" tests/arith.sh slice
    step progtest tests/par.sh tests/progtest.sh tests/c/prog/*.c
    # Small constant copies (docs/perf.md item 7a): the failing cases,
    # inline filter against --memcpy=call.
    step memcpy tests/memcpy.sh
    # Access checks of at most 16 bytes without the borrow test (item 6a):
    # their boundaries, -O against the reference selection.
    step checks tests/checks.sh
    # c-testsuite/00200 (1557 blocks) is the slowest compile (docs/m5.md).
    step corpus env COMPILE_TIMEOUT=60 python3 -I tests/corpus.py ${corpus.cproc} ${corpus.c-testsuite}
    # GLib resource blobs of gtk4's size (1.66 MB), in both of
    # glib-compile-resources' forms: each overflowed the 1 GB stack. They
    # compile within 700 MB, so a real one (with its headers) has room.
    python3 -I tests/bigblob.py string 1700000 > bigblob-string.c
    python3 -I tests/bigblob.py braces 1700000 > bigblob-braces.c
    # A non-byte table (800k unsigned shorts) is one data chunk too.
    python3 -I tests/bigblob.py shorts 800000 > bigblob-shorts.c
    step bigblob env COMPILE_TIMEOUT=300 NANOFIL_STACK_LIMIT=734003200 \
      tests/progtest.sh bigblob-string.c bigblob-braces.c bigblob-shorts.c
    # One basic block of 3000 statements (tor's keccak-tiny-unrolled.c):
    # block liveness was quadratic in its length (docs/perf.md, item 15).
    python3 -I tests/longblock.py 1500 > longblock.c
    step longblock env COMPILE_TIMEOUT=60 tests/progtest.sh longblock.c
    step "progtest gc-stress" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    step "run-c gc gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh gc
    # M5: the same suites with the middle end on. difftest -O also runs
    # every run line on the unoptimized module and checks that each result
    # refines it; unit.pl checks promotion, copy removal, exact pointer
    # identity and bounded symbolic before/after equivalence.
    python3 -I tests/bigfn.py 1 300 > big1.c
    export NANOFIL_OPT=-O
    # A 32 KB struct copied by value (minizip's zipOpen3): one function of
    # 16k loads and stores, each its own register-home candidate, within
    # SWI's default 1 GB stack (docs/perf.md, item 11).
    python3 -I tests/bigcopy.py 32768 > bigcopy.c
    # 2000 ints live together, each written twice: about 2M interference
    # pairs between register-home candidates (netcdf's tst_h_atts.c,
    # openssh's libcrux; docs/perf.md, item 13).
    python3 -I tests/manyhomes.py 2000 > manyhomes.c
    step "-O bigcopy manyhomes 1 GB" env COMPILE_TIMEOUT=300 NANOFIL_STACK_LIMIT=1073741824 \
      tests/progtest.sh bigcopy.c manyhomes.c
    step "-O difftest float SSE2" env CC=$CC tests/difftest.sh tests/float/*.ir
    step "-O difftest fixtures+gen1" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir
    step "-O difftest backend" env CC=$CC tests/par.sh tests/difftest.sh tests/backend/*.ir
    step "-O difftest filc, c, big1" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/asm-fixed-runs.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/guard-span.ir tests/c/*.c big1.c
    step "-O run-c interop gc float" tests/par.sh tests/filc/run-c.sh interop gc float asm-fixed
    step "-O variadic+float gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh variadic float
    step "-O setjmp gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh setjmp
    step "-O pointer+exception gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh pointer-effects lower-donor exceptions
    step "-O actual ensure-aux exits" tests/filc/trace-pointer-effects.sh
    step "-O progtest" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    step "-O progtest gc-stress" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    step "-O run-c gc gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh gc
    # Inlining (docs/perf.md item 4) is the -O default, so the -O suites
    # above inline; these keep -O --inline=none, the uninlined path.
    export NANOFIL_INLINE=none
    step "-O inline=none difftest" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
    step "-O inline=none ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
    step "-O inline=none programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    unset NANOFIL_INLINE
    # The cheap middle end (docs/perf.md item 8) is the -O default, so the
    # -O suites above simplify; these keep -O --simplify=none.
    export NANOFIL_SIMPLIFY=none
    step "-O simplify=none difftest" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir tests/backend/*.ir tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/branches.ir tests/c/*.c big1.c
    step "-O simplify=none ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
    step "-O simplify=none programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    unset NANOFIL_SIMPLIFY
    # Register homes with register operands and frame cells on a frame
    # with a home per scalar temporary and pointer address words as homes
    # too (--registers=pointers, docs/perf.md items 3, 5a-loads, 3d and
    # 5b-2) are the -O default, so the -O suites above run them, validated
    # by amd64_regs_check; here temps runs without and with -O (scalar
    # homes only) and -O runs the stack reference. The modes local,
    # function, operands, cells and flow were retired (docs/perf.md,
    # register modes); tests/registers.sh shows they are refused.
    step "retired registers" tests/registers.sh
    for mode in "temps:" "stack:-O" "temps:-O"; do
      export NANOFIL_REGISTERS=''${mode%%:*} NANOFIL_OPT=''${mode#*:}
      step "registers $mode difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/branches.ir tests/c/*.c big1.c
      step "registers $mode ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc asm-fixed
      step "registers $mode actual ensure-aux exits" tests/filc/trace-pointer-effects.sh
      step "registers $mode memcpy" tests/memcpy.sh
      step "registers $mode checks" tests/checks.sh
      step "registers $mode programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    done
    unset NANOFIL_OPT
    export NANOFIL_REGISTERS=temps
    step "temps corpus" env COMPILE_TIMEOUT=60 python3 -I tests/corpus.py ${corpus.cproc} ${corpus.c-testsuite}
    unset NANOFIL_REGISTERS
    # M7 check reuse (docs/m7.md) is independent of both. difftest also
    # runs each run line on the reused module, which must agree with the
    # unchecked one, traps included; the native suites cover helper exits
    # and collection, which the interpreter abstracts.
    export NANOFIL_CHECKS=reuse
    for opt in "" -O; do
      export NANOFIL_OPT=$opt
      step "reuse $opt difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
      step "reuse $opt ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
      step "reuse $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    done
    unset NANOFIL_OPT
    step "reuse corpus" env COMPILE_TIMEOUT=60 python3 -I tests/corpus.py ${corpus.cproc} ${corpus.c-testsuite}
    step "reuse temps ABI+GC" env NANOFIL_REGISTERS=temps RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh gc setjmp pointer-effects reuse-gc
    unset NANOFIL_CHECKS
    # M7 round 4, check renewal (docs/m7.md): reuse, then a check that a
    # dominating check covers tests only free and read-only. It is the
    # -O default, so the -O suites above run it; here it runs without
    # -O, where reuse-gc.ir's reads after c_gc are renewed (-O promotes
    # its allocations), so P must stay rooted across collections, and
    # -O keeps a run with reference checks. renew-trap.sh compares trap
    # text with reference.
    export NANOFIL_CHECKS=renew
    step "renew difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
    step "renew ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
    step "renew programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    step "renew temps ABI+GC" env NANOFIL_REGISTERS=temps RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh gc setjmp pointer-effects reuse-gc
    export NANOFIL_CHECKS=reference NANOFIL_OPT=-O
    step "-O reference checks difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
    step "-O reference checks ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
    step "-O reference checks programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    unset NANOFIL_CHECKS NANOFIL_OPT
    # M7 round 5, range guards (docs/m7.md): renewal, then a span test
    # before each loop and renew_if for the loop's checks it covers. The
    # corpus compiles under -O, where the guards apply, so the validator
    # sees every guard the pass makes; renew-trap.sh compares guarded
    # traps with reference too.
    export NANOFIL_CHECKS=guard
    for opt in "" -O; do
      export NANOFIL_OPT=$opt
      step "guard $opt difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/guard-span.ir tests/c/*.c big1.c
      step "guard $opt ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
      step "guard $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    done
    step "guard -O corpus" env COMPILE_TIMEOUT=60 python3 -I tests/corpus.py ${corpus.cproc} ${corpus.c-testsuite}
    unset NANOFIL_OPT NANOFIL_CHECKS
    step "renew and guard trap text" tests/renew-trap.sh
    # Branch selection (docs/perf.md) is the -O default, so the -O suites
    # above run it; here it runs without -O, and -O runs the reference
    # branches, whose stream temps' checkers validate.
    for mode in "selected:" "reference:-O"; do
      export NANOFIL_BRANCHES=''${mode%%:*} NANOFIL_OPT=''${mode#*:}
      step "branches $mode difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/branches.ir tests/c/*.c big1.c
      step "branches $mode ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
      step "branches $mode programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/progtest.sh tests/c/prog/*.c
    done
    unset NANOFIL_OPT
    export NANOFIL_BRANCHES=selected
    step "branches corpus" env COMPILE_TIMEOUT=60 python3 -I tests/corpus.py ${corpus.cproc} ${corpus.c-testsuite}
    unset NANOFIL_BRANCHES
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
