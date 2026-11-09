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
#
# The steps are independent once the setup below has run: each needs
# only the saved state, the generated inputs and its own exports. With
# shard = "I/N" the derivation runs shard I of N (1-based), a fixed
# split of the step list balanced by tests/check-times.tsv, and keeps
# going past a failing step; the N shards together run every step once
# (.github/workflows/nanofil.yml runs them side by side). Each step prints
# a "@@nanofil-step ok|FAIL SECONDS LABEL" line for aggregation.
{
  pkgs,
  filcc,
  withTrealla ? false,
  shard ? null,
}:
let
  trealla = import ./trealla.nix { inherit pkgs; };
  corpus = import ./corpus.nix { inherit pkgs; };
  shardName = builtins.replaceStrings [ "/" ] [ "-of-" ] shard;
in
pkgs.runCommandCC
  (if shard == null then "nanofil-check" else "nanofil-check-${shardName}")
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      (pkgs.python3.withPackages (p: [ p.z3-solver ]))
      pkgs.gdb
    ]
    ++ pkgs.lib.optional withTrealla trealla;
  }
  ''
    # step LABEL CMD...: run CMD, printing when it starts and how long it
    # took as soon as it ends (watch with nix build -L); the table at the
    # end sums it up. With $listing set it only prints LABEL; with
    # $selected set it skips steps not listed in that file.
    check_t0=$SECONDS failed=
    step() {
      local label=$1 t0=$SECONDS status=ok mark=
      shift
      if [ -n "''${listing-}" ]; then
        printf '%s\n' "$label"
        return
      fi
      if [ -n "''${selected-}" ] && ! grep -Fxq -- "$label" "$selected"; then
        return
      fi
      echo ">>> [$((SECONDS - check_t0))s] start: $label"
      python3 tests/watch.py --label "$label" --warn-after 300 --timeout 1800 -- "$@" || status=FAIL mark=" FAILED"
      echo "<<< [$((SECONDS - check_t0))s] done in $((SECONDS - t0))s: $label$mark"
      printf '%5ds  %s\n' $((SECONDS - t0)) "$label$mark" >>"$TMPDIR/timings"
      echo "@@nanofil-step $status $((SECONDS - t0)) $label"
      if [ $status = FAIL ]; then
        failed="$failed''${failed:+, }$label"
        ${if shard == null then "exit 1" else "return 0"}
      fi
    }
    # Keep each complete mode, but distribute its independent files across
    # four steps. Round-robin sorted paths spread the vector family across
    # groups; each file and each step keeps its original deadline.
    programs() {
      local label=$1 part i
      shift
      local files=(tests/c/prog/*.c) group
      for part in 1 2 3 4; do
        group=()
        for ((i = part - 1; i < ''${#files[@]}; i += 4)); do
          group+=("''${files[i]}")
        done
        step "$label [$part/4]" "$@" tests/par.sh tests/progtest.sh "''${group[@]}"
      done
    }
    corpus_steps() {
      local label=$1 part
      for part in 1 2 3 4; do
        step "$label [$part/4]" python3 -I tests/corpus.py \
          ${corpus.cproc} ${corpus.c-testsuite} --partition "$part/4"
      done
    }
    cp -r ${../.} nanofil
    chmod -R u+w nanofil
    cd nanofil
    patchShebangs tests bin
    # Wall-clock limits that catch hangs, not slowness: CI runs a shard on
    # 4 vCPUs that eight parallel compiles share (bounds edges), where a
    # 30 s compile takes over 60 s and a step that takes 2 minutes on an
    # orb takes over 5. Below tests/par.sh's 300 s per file, so a compile
    # timeout is reported as such.
    export COMPILE_TIMEOUT=240 PROG_TIMEOUT=60
    # Commands run from a saved state (bin/nanofil); scripts still load
    # src/, so both paths are tested.
    bin/nanofil --save-state "$TMPDIR/nanofil.state"
    export NANOFIL_STATE=$TMPDIR/nanofil.state
    # Generated inputs, described at the steps that use them.
    (cd src && ../bin/nanofil --script ../tests/gen.pl 1 200 </dev/null) > gen1.ir
    python3 -I tests/bigblob.py string 1700000 > bigblob-string.c
    python3 -I tests/bigblob.py braces 1700000 > bigblob-braces.c
    # A non-byte table (800k unsigned shorts) is one data chunk too.
    python3 -I tests/bigblob.py shorts 800000 > bigblob-shorts.c
    python3 -I tests/longblock.py 1500 > longblock.c
    python3 -I tests/bigfn.py 1 300 > big1.c
    python3 -I tests/bigcopy.py 32768 > bigcopy.c
    python3 -I tests/manyhomes.py 2000 > manyhomes.c
    python3 -I tests/ifchain.py 600 > ifchain.c
    python3 -I tests/bigfn.py 2 100 > big2.c
    steps() {
    step "check watchdog" bash -c 'python3 tests/watch_test.py && python3 tests/harness_test.py'
    step unit bash -c '(cd src && ../bin/nanofil --script ../tests/unit.pl </dev/null) | tee unit.log && grep -q "tests ok$" unit.log'
    # Every module has a header and every export PlDoc (docs/guide.md,
    # Conventions).
    step docs swipl tests/docs.pl -- src
    # Every predicate, module, link and concept reference in the guide,
    # the formal campaign and the concepts resolves, as does every
    # [[concept]] in a Prolog or Rocq comment, and each prolog output has
    # its terms (web/dterm_guide.pl).
    step "guide links" swipl web/dterm.pl --check docs/guide.md docs/formal.md docs/filc.md docs/iris.md src \
      --concepts=docs/concepts --rocq=rocq/theories
    # M9 interpreter against nanofil's SSE2 backend.
    # Integer-bit wrappers preserve NaN payloads and negative zero.
    step "difftest float SSE2" env CC=$CC tests/difftest.sh tests/float/*.ir
    step "difftest fixtures+gen1" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir
    step "difftest backend" env CC=$CC tests/par.sh tests/difftest.sh tests/backend/*.ir
    export FILCC=${filcc}/bin/clang
    step pptest tests/pptest.sh
    # The guide's example outputs (docs/guide.md, README.md) are what the
    # compiler now produces.
    step guide tests/guide.sh --check
    step "difftest filc/*.ir" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/asm-fixed-runs.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/guard-span.ir tests/filc/branches.ir tests/filc/alloc-limit.ir
    step "run-c interop gc float" tests/par.sh tests/filc/run-c.sh interop gc float asm-fixed
    step "variadic+float gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh variadic float
    step "setjmp gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh setjmp
    step "pointer+exception gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh pointer-effects lower-donor exceptions reuse-gc lowers
    step "actual ensure-aux exits" tests/filc/trace-pointer-effects.sh
    step "difftest c/*.c" tests/par.sh tests/difftest.sh tests/c/*.c
    step reject tests/reject.sh
    # const_eval, the IR and clang on generated integer expressions (docs/arith.md).
    step "arith slice" tests/arith.sh slice
    programs progtest
    # Every bounds-check shape's lines against Fil-C's condition, with Z3
    # (docs/bounds.md). Partition by size, not shape: merged dominates.
    step "bounds smt" python3 tests/bounds_smt.py --parallel
    # Every hoisted shape's limit and in-loop lines against Fil-C's full
    # check at the access, with Z3 (docs/bounds.md, hoisted bounds).
    step "hoist smt" python3 tests/hoist_smt.py --parallel
    # Both half checks' lines against Fil-C's full check, given the bound
    # an earlier check of the object proves, with Z3 (docs/half.md).
    step "half smt" python3 tests/half_smt.py --parallel
    # Every bounds-check shape at both levels against filcc's traps
    # (docs/bounds.md). Each mode forks thousands of children: independent
    # steps avoid eight simultaneous fork storms in one builder.
    for b in split merged sign or; do
      for o in "" -O; do
        step "bounds edges $b ''${o:-plain}" env NANOFIL_BOUNDS=$b NANOFIL_OPT=$o tests/progtest.sh tests/c/bounds/edges.c
      done
    done
    # The same matrix with each access in a loop, hoisted (docs/bounds.md;
    # -O keeps the loop's base in a register, which hoisting needs).
    for b in split merged sign or; do
      step "hoisted bounds edges $b" env NANOFIL_CHECKS=hoist NANOFIL_BOUNDS=$b NANOFIL_OPT=-O tests/progtest.sh tests/c/bounds/hoist-edges.c
    done
    # Small constant copies (docs/perf.md item 7a): the failing cases,
    # inline filter against --memcpy=call.
    step memcpy tests/memcpy.sh
    # Access checks of at most 16 bytes without the borrow test (item 6a):
    # their boundaries, -O against the reference selection.
    step checks tests/checks.sh
    # c-testsuite/00200 (1557 blocks) is the slowest compile (docs/m5.md).
    corpus_steps corpus
    # GLib resource blobs of gtk4's size (1.66 MB), in both of
    # glib-compile-resources' forms: each overflowed the 1 GB stack. They
    # compile within 700 MB, so a real one (with its headers) has room.
    # Each file has its own compiler stack and differential run directory.
    step bigblob env COMPILE_TIMEOUT=300 NANOFIL_STACK_LIMIT=734003200 \
      tests/par.sh tests/progtest.sh bigblob-string.c bigblob-braces.c bigblob-shorts.c
    # One basic block of 3000 statements (tor's keccak-tiny-unrolled.c):
    # block liveness was quadratic in its length (docs/perf.md, item 15).
    step longblock env COMPILE_TIMEOUT=60 tests/progtest.sh longblock.c
    programs "progtest gc-stress" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    step "run-c gc gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh gc
    # M5: the same suites with the middle end on. difftest -O also runs
    # every run line on the unoptimized module and checks that each result
    # refines it; unit.pl checks promotion, copy removal, exact pointer
    # identity and bounded symbolic before/after equivalence.
    export NANOFIL_OPT=-O
    # A 32 KB struct copied by value (minizip's zipOpen3): one function of
    # 16k loads and stores, each its own register-home candidate, within
    # SWI's default 1 GB stack (docs/perf.md, item 11).
    # 2000 ints live together, each written twice: about 2M interference
    # pairs between register-home candidates (netcdf's tst_h_atts.c,
    # openssh's libcrux; docs/perf.md, item 13).
    step "-O bigcopy manyhomes 1 GB" env COMPILE_TIMEOUT=300 NANOFIL_STACK_LIMIT=1073741824 \
      tests/progtest.sh bigcopy.c manyhomes.c
    # 600 if arms reading one struct around calls: renewal's dominance
    # test is an interval lookup, not a walk per (check, source) pair
    # (docs/perf.md, item 18), 10 s where the walk took 189 s.
    step "-O ifchain 600 compile time" env COMPILE_TIMEOUT=60 tests/progtest.sh ifchain.c
    step "-O difftest float SSE2" env CC=$CC tests/difftest.sh tests/float/*.ir
    step "-O difftest fixtures+gen1" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir
    step "-O difftest backend" env CC=$CC tests/par.sh tests/difftest.sh tests/backend/*.ir
    step "-O difftest filc, c, big1" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/asm-fixed-runs.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/guard-span.ir tests/filc/alloc-limit.ir tests/c/*.c big1.c
    step "-O run-c interop gc float" tests/par.sh tests/filc/run-c.sh interop gc float asm-fixed
    step "-O variadic+float gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh variadic float
    step "-O setjmp gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh setjmp
    step "-O pointer+exception gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh pointer-effects lower-donor exceptions lowers
    step "-O actual ensure-aux exits" tests/filc/trace-pointer-effects.sh
    programs "-O progtest"
    programs "-O progtest gc-stress" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    # The merged and or bounds checks (docs/bounds.md), opt-in.
    programs "-O merged bounds programs" env NANOFIL_BOUNDS=merged
    programs "-O or bounds programs" env NANOFIL_BOUNDS=or
    step "-O run-c gc gc-stress" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh gc
    # Wide inlining (docs/perf.md items 4 and 20) is the -O default, so
    # the -O suites above inline; these keep -O --inline=none, the
    # uninlined path, and then small, item 4's leaves.
    export NANOFIL_INLINE=none
    step "-O inline=none difftest" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
    step "-O inline=none ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
    programs "-O inline=none programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    export NANOFIL_INLINE=small
    step "-O inline=small difftest" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir tests/c/*.c big1.c
    programs "-O inline=small programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    unset NANOFIL_INLINE
    # The cheap middle end (docs/perf.md item 8) is the -O default, so the
    # -O suites above simplify; these keep -O --simplify=none.
    export NANOFIL_SIMPLIFY=none
    step "-O simplify=none difftest" env CC=$CC tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir tests/backend/*.ir tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/branches.ir tests/c/*.c big1.c
    step "-O simplify=none ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
    programs "-O simplify=none programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
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
      programs "registers $mode programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    unset NANOFIL_OPT
    export NANOFIL_REGISTERS=temps
    corpus_steps "temps corpus"
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
      programs "reuse $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    unset NANOFIL_OPT
    corpus_steps "reuse corpus"
    step "reuse temps ABI+GC" env NANOFIL_REGISTERS=temps RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh gc setjmp pointer-effects reuse-gc
    unset NANOFIL_CHECKS
    # M7 round 4, check renewal (docs/m7.md): reuse, then a check that a
    # dominating check covers tests only free and read-only. It was the
    # -O default before combined; it runs here without -O, where
    # reuse-gc.ir's reads after c_gc are renewed (-O promotes its
    # allocations), so P must stay rooted across collections, and with
    # -O and nothing shared, the previous default. -O also keeps a run
    # with reference checks. renew-trap.sh compares trap text with
    # reference.
    export NANOFIL_CHECKS=renew NANOFIL_SHARE=none
    for opt in "" -O; do
      export NANOFIL_OPT=$opt
      step "renew $opt difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
      step "renew $opt ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
      programs "renew $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    unset NANOFIL_OPT
    step "renew temps ABI+GC" env NANOFIL_REGISTERS=temps RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh gc setjmp pointer-effects reuse-gc
    # Combined checks (forward facts, then half checks) are the -O
    # default with shared check parts, so the -O suites above run them;
    # here they run without -O, where nothing is shared.
    export NANOFIL_CHECKS=combined
    step "combined difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
    step "combined ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
    programs "combined programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    step "combined temps ABI+GC" env NANOFIL_REGISTERS=temps RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh gc setjmp pointer-effects reuse-gc
    export NANOFIL_CHECKS=reference NANOFIL_OPT=-O
    step "-O reference checks difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
    step "-O reference checks ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
    programs "-O reference checks programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    unset NANOFIL_CHECKS NANOFIL_OPT NANOFIL_SHARE
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
      programs "guard $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    corpus_steps "guard -O corpus"
    unset NANOFIL_OPT NANOFIL_CHECKS
    # Hoisted bounds (docs/bounds.md): renewal, then a limit before each
    # loop and check_limit for the loop's remaining full checks of a root
    # defined before it. The corpus compiles under -O, so the validator
    # sees every limit the pass makes; renew-trap.sh compares hoisted
    # traps with reference too.
    export NANOFIL_CHECKS=hoist
    for opt in "" -O; do
      export NANOFIL_OPT=$opt
      step "hoist $opt difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
      step "hoist $opt ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
      programs "hoist $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    corpus_steps "hoist -O corpus"
    unset NANOFIL_OPT NANOFIL_CHECKS
    # Scheduled checks (docs/schedule.md), opt-in: renewal, then checks
    # widened over the bytes every path ahead needs and renewed at a
    # distance. difftest's oracle accepts an earlier trap only where the
    # unchecked run traps; schedule-trap.sh compares traps with filcc -O2.
    export NANOFIL_CHECKS=schedule
    for opt in "" -O; do
      export NANOFIL_OPT=$opt
      step "schedule $opt difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
      step "schedule $opt ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
      programs "schedule $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    corpus_steps "schedule -O corpus"
    unset NANOFIL_OPT NANOFIL_CHECKS
    # Shared check parts (docs/perf.md item 17), the -O default with
    # combined checks: a check skips the null test of a lower a dominating
    # check tested, and reuses the upper the check just before it loaded
    # for the same object. These are the -O default's own runs: the corpus
    # compiles under -O, where the register checkers validate every
    # stream; share-trap.sh compares traps with filcc, and share_smt.py
    # proves the shortened lines against Fil-C's condition.
    export NANOFIL_SHARE=upper NANOFIL_OPT=-O
    step "share difftest" tests/par.sh tests/difftest.sh tests/filc/share.ir tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
    step "share ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
    programs "share programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    step "share checks" tests/checks.sh
    step "share temps checks" env NANOFIL_REGISTERS=temps tests/checks.sh
    corpus_steps "share -O corpus"
    unset NANOFIL_OPT NANOFIL_SHARE
    step "share smt" python3 tests/share_smt.py
    # Shared lowers (docs/lowers.md), opt-in: a flight or phi uses its
    # lower root's lowers[] entry, kept while it is live, and
    # lowers_check validates every frame (a rejection fails the
    # compile). The corpus compiles under -O, so the checker sees every
    # frame the producer makes; lowers.ir has a root dead, and one
    # written again, while its flight is live across a collection.
    export NANOFIL_LOWERS=shared
    for opt in "" -O; do
      export NANOFIL_OPT=$opt
      step "lowers $opt difftest" tests/par.sh tests/difftest.sh tests/fixtures/*.ir gen1.ir tests/backend/*.ir tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/share.ir tests/filc/branches.ir tests/c/*.c big1.c
      step "lowers $opt ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc lowers asm-fixed
      step "lowers $opt actual ensure-aux exits" tests/filc/trace-pointer-effects.sh
      programs "lowers $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    corpus_steps "lowers -O corpus"
    step "lowers temps ABI+GC" env NANOFIL_REGISTERS=temps RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh gc setjmp pointer-effects reuse-gc lowers
    unset NANOFIL_OPT NANOFIL_LOWERS
    step "share trap text vs filcc" tests/share-trap.sh
    # Half checks (docs/half.md), opt-in: renewal, then each check of an
    # object an earlier dominating check proved at another range tests only
    # the bound that check leaves unknown. renew-trap.sh compares their
    # traps with reference checks, byte for byte.
    export NANOFIL_CHECKS=half
    for opt in "" -O; do
      export NANOFIL_OPT=$opt
      step "half $opt difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
      step "half $opt ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
      programs "half $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    corpus_steps "half -O corpus"
    unset NANOFIL_OPT NANOFIL_CHECKS
    step "schedule trap text vs filcc -O2" tests/schedule-trap.sh
    # Forward facts (docs/forward.md), opt-in: reuse that also serves
    # heap pointer loads and covers a check by the hull of its object's
    # live facts, then renewal. No trap moves; renew-trap.sh compares
    # forward-*.c's trap text with reference.
    export NANOFIL_CHECKS=forward
    for opt in "" -O; do
      export NANOFIL_OPT=$opt
      step "forward $opt difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
      step "forward $opt ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
      programs "forward $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    corpus_steps "forward -O corpus"
    unset NANOFIL_OPT NANOFIL_CHECKS
    # Renewal by the hull of two checks and facts kept across repeated
    # getters (docs/forward.md), opt-in as --checks=extended (both),
    # hull and getter. renew-trap.sh compares hull-*.c's traps with
    # reference checks, getter-trap.sh a getter whose ifunc resolver frees.
    export NANOFIL_CHECKS=extended
    for opt in "" -O; do
      export NANOFIL_OPT=$opt
      step "extended $opt difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/c/*.c big1.c
      step "extended $opt ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
      programs "extended $opt programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    corpus_steps "extended -O corpus"
    step "extended -O ifchain 600 compile time" env NANOFIL_OPT=-O COMPILE_TIMEOUT=60 tests/progtest.sh ifchain.c
    unset NANOFIL_OPT NANOFIL_CHECKS
    step "getter trap text" tests/getter-trap.sh
    step "renew, guard, hoist, half, forward combined and hull trap text" tests/renew-trap.sh
    step "hoist trap text, every shape" bash -c 'for b in merged or sign; do NANOFIL_BOUNDS=$b tests/renew-trap.sh || exit 1; done'
    # Branch selection (docs/perf.md) is the -O default, so the -O suites
    # above run it; here it runs without -O, and -O runs the reference
    # branches, whose stream temps' checkers validate.
    for mode in "selected:" "reference:-O"; do
      export NANOFIL_BRANCHES=''${mode%%:*} NANOFIL_OPT=''${mode#*:}
      step "branches $mode difftest" tests/par.sh tests/difftest.sh tests/filc/basic.ir tests/filc/globals.ir tests/filc/tuples.ir tests/filc/copy.ir tests/filc/local.ir tests/filc/check-range.ir tests/filc/reuse.ir tests/filc/reuse-offset.ir tests/filc/shadows.ir tests/filc/branches.ir tests/c/*.c big1.c
      step "branches $mode ABI+GC" env RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/par.sh tests/filc/run-c.sh interop gc variadic float setjmp pointer-effects lower-donor exceptions reuse-gc
      programs "branches $mode programs" env RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1"
    done
    unset NANOFIL_OPT
    export NANOFIL_BRANCHES=selected
    corpus_steps "branches corpus"
    unset NANOFIL_BRANCHES
    # The functional, versioned-fact and incremental analyses must agree.
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
    }
    (listing=1 steps) >"$TMPDIR/steps"
    # A label names its step in a shard's selection, so each is unique.
    if sort "$TMPDIR/steps" | uniq -d | grep .; then
      echo "nanofil check: duplicate step labels above" >&2
      exit 1
    fi
    echo "@@nanofil-steps $(wc -l <"$TMPDIR/steps") $(sha256sum <"$TMPDIR/steps" | cut -c1-16)"
    ${pkgs.lib.optionalString (shard != null) ''
      selected=$TMPDIR/selected
      tests/check-plan.sh ${shard} <"$TMPDIR/steps" >"$selected"
      echo "@@nanofil-shard ${shard} $(wc -l <"$selected") steps"
    ''}
    steps
    echo "== nanofil check timings"
    cat "$TMPDIR/timings"
    if [ -n "$failed" ]; then
      echo "@@nanofil-failed $failed"
      exit 1
    fi
    touch $out
  ''
