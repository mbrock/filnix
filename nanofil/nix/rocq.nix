# The Rocq model of the checked IR (rocq/, docs/formal.md Campaign 1):
# default: model + parse.sh + a small outcome/base-verdict smoke corpus.
# full=true opts into the complete outcome and mutation campaign below:
# compile it with the pinned nixpkgs' Rocq, refuse any Admitted or Axiom
# (none is allowed outside the Campaign 2 runtime module type, which
# does not exist yet), extract and link the model, then check that it
# agrees with interp:run/5 on every run line of rocq/tests, the Fil-C
# IR fixtures, the C tests and Fil-C modules from tests/gen.pl, the
# last three with and without -O and under every --checks mode
# (rocq/agree.sh), and Lua's own functions (rocq/lua.sh); and that its
# validator reaches ir:valid_module/1's verdict on mutants of every checked module
# in the same matrix, and of the tests/c/prog programs with aliases and
# weak, thread-local or constructor data (rocq/valid.sh).
{
  pkgs,
  filcc,
  full ? false,
}:
let
  rocq = pkgs.rocqPackages;
  ocamlPackages = rocq.rocq-core.ocamlPackages;
  model = pkgs.stdenv.mkDerivation {
    name = "nanofil-rocq-model";
    # Fixtures and shell harnesses do not change the extracted executable.
    src = pkgs.lib.fileset.toSource {
      root = ../rocq;
      fileset = pkgs.lib.fileset.unions [
        ../rocq/Makefile
        ../rocq/_RocqProject
        ../rocq/theories
        ../rocq/extraction/main.ml
      ];
    };
    nativeBuildInputs = [
      rocq.rocq-core
      rocq.stdlib
      ocamlPackages.ocaml
      ocamlPackages.findlib
      pkgs.python3
    ];
    buildInputs = [ ocamlPackages.zarith ];
    buildPhase = ''
      if grep -rnwE 'Admitted|Axiom|Axioms|Parameter|Conjecture' theories; then
        echo "rocq: no Admitted or Axiom outside the runtime module type" >&2
        exit 1
      fi
      start=$SECONDS
      python3 ${../tests/watch.py} --label "Rocq compile/extraction/link" -- make
      echo "@@nanofil-rocq $((SECONDS - start))s compile-extract-link"
    '';
    installPhase = ''
      mkdir -p $out/bin
      cp nanofil-model $out/bin/
    '';
  };
  # The check reads compiler sources, harnesses and corpora, not the wiki,
  # benchmarks or theories (the latter enter through model above).
  corpus = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../src
      ../bin
      ../tests
      ../rocq/agree.sh
      ../rocq/valid.sh
      ../rocq/lua.sh
      ../rocq/mutants.pl
      ../rocq/tests
    ];
  };
  syntax = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../rocq/_RocqProject
      ../rocq/theories
      ../rocq/extraction/main.ml
      ../web/rocq/rocq_syntax.pl
      ../web/rocq/tests/parse.sh
      ../web/rocq/tests/reprint.pl
    ];
  };
in
pkgs.runCommandCC
  (if full then "nanofil-rocq-full-check" else "nanofil-rocq-check")
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      pkgs.python3
      rocq.rocq-core
      rocq.stdlib
    ];
    passthru = { inherit model; };
  }
  (
    ''
      set -o pipefail
      start=$SECONDS
      mark() {
        echo "@@nanofil-rocq $((SECONDS - start))s $*"
        start=$SECONDS
      }
      cp -r ${corpus} nanofil
      chmod -R u+w nanofil
      cp -r ${syntax}/. nanofil/
      chmod -R u+w nanofil
      cd nanofil
      patchShebangs rocq bin tests
      export FILCC=${filcc}/bin/clang MODEL=${model}/bin/nanofil-model
      bin/nanofil --save-state "$TMPDIR/nanofil.state"
      export NANOFIL_STATE=$TMPDIR/nanofil.state
      python3 tests/watch.py --label "Rocq parse/typecheck" -- bash web/rocq/tests/parse.sh
      mark parse
    ''
    + (
      if !full then
        ''
          # A deliberately small, stable smoke corpus: every hand-written model
          # fixture plus ordinary checked IR, long doubles and data/aliases.
          export NANOFIL_CHECKS=reference NANOFIL_JOBS=$NIX_BUILD_CORES NANOFIL_MUTANTS=0
          tests/par.sh rocq/agree.sh rocq/tests/*.ir tests/filc/basic.ir tests/c/ldouble.c tests/c/prog/alias.c \
            | tee "$TMPDIR/quick-outcomes.log"
          tests/par.sh rocq/valid.sh rocq/tests/*.ir tests/filc/basic.ir tests/c/ldouble.c tests/c/prog/alias.c \
            | tee "$TMPDIR/quick-valid.log"
          mkdir -p $out
          cp "$TMPDIR"/quick-*.log $out/
          mark quick-base-verdicts
        ''
      else
        ''
          python3 tests/watch.py --label "mutant partition coverage" -- bash rocq/tests/partitions.sh
          # Hand-written checked IR (rocq/tests) goes in as written: the check
          # passes take pizlonate's output, never renew_hull or renew_if.
          NANOFIL_CHECKS=reference NANOFIL_JOBS=$NIX_BUILD_CORES tests/par.sh rocq/agree.sh rocq/tests/*.ir
          # Forty Fil-C modules of ten random functions (tests/gen.pl's filc
          # mode), which trap often and reach every reuse form, join the
          # matrix below.
          mkdir gen
          for seed in $(seq 1 40); do
            (cd src && ../bin/nanofil --script ../tests/gen.pl $seed 10 filc </dev/null) > gen/gen-$seed.ir
          done
          # Lua 5.4.7's lctype.c, lobject.c and lstring.c, the source nix/lua.nix
          # builds, with the run lines of rocq/tests/lua.c, join the outcome
          # matrix; the validator judges their mutants once, below, since each
          # is judged on the whole module.
          mkdir luasrc
          tar -xf ${pkgs.lua5_4.src} -C luasrc --strip-components=1
          rocq/lua.sh luasrc/src >lua.ir
          mark prepare
          # Modes are independent, just as in the validator matrix below. Keep
          # each mode's complete log and propagate any failing xargs child.
          for opt in plain -O; do
            for checks in reference reuse renew guard hoist schedule half forward combined hull getter extended; do
              echo "$opt $checks"
            done
          done | xargs -P "$NIX_BUILD_CORES" -L 1 bash -c '
            set -o pipefail
            opt=$0; [ "$opt" = plain ] && opt=
            t0=$(date +%s)
            NANOFIL_OPT=$opt NANOFIL_CHECKS=$1 NANOFIL_JOBS=1 tests/par.sh rocq/agree.sh tests/filc/*.ir tests/c/*.c gen/*.ir lua.ir \
              2>&1 | tee "$TMPDIR/agree-$0-$1.log" | grep --line-buffered "^@@nanofil-" \
              || { echo "### agree NANOFIL_OPT=$opt NANOFIL_CHECKS=$1"; cat "$TMPDIR/agree-$0-$1.log"; exit 1; }
            echo "agree NANOFIL_OPT=$opt NANOFIL_CHECKS=$1: $(grep -c "^/" "$TMPDIR/agree-$0-$1.log") files agree ($(( $(date +%s) - t0 ))s)"'
          mark outcomes
          # The validator against ir:valid_module/1 on mutants of every checked
          # module (rocq/valid.sh, rocq/mutants.pl), in every mode at once.
          NANOFIL_CHECKS=reference NANOFIL_JOBS=$NIX_BUILD_CORES tests/par.sh rocq/valid.sh rocq/tests/*.ir
          # (xargs drops empty words, so "plain" stands for no -O.)
          for opt in plain -O; do
            for checks in reference reuse renew guard hoist schedule half forward combined hull getter extended; do
              echo "$opt $checks"
            done
          done | xargs -P "$NIX_BUILD_CORES" -L 1 bash -c '
            set -o pipefail
            opt=$0; [ "$opt" = plain ] && opt=
            t0=$(date +%s)
            NANOFIL_OPT=$opt NANOFIL_CHECKS=$1 NANOFIL_JOBS=1 tests/par.sh rocq/valid.sh tests/filc/*.ir tests/c/*.c gen/*.ir \
              2>&1 | tee "$TMPDIR/valid-$0-$1.log" | grep --line-buffered "^@@nanofil-" \
              || { echo "### valid NANOFIL_OPT=$opt NANOFIL_CHECKS=$1"; cat "$TMPDIR/valid-$0-$1.log"; exit 1; }
            echo "valid NANOFIL_OPT=$opt NANOFIL_CHECKS=$1: $(grep -c "^/" "$TMPDIR/valid-$0-$1.log") files agree ($(( $(date +%s) - t0 ))s)"'
          mark validator-matrix
          # The C programs of tests/c/prog that declare an alias, a weak
          # symbol, thread-local data or a constructor, with the reference
          # checks only: they bring the corpus's aliases and its kinds of data
          # linkage. Not those with a "// cflags:" line, which compile as
          # progtest.sh does and not as cc-ir does.
          grep -lE 'alias *\(|weak|_Thread_local|__thread|thread_local|constructor|destructor' \
            $(grep -L '^// cflags:' tests/c/prog/*.c) >prog.list
          xargs -P "$NIX_BUILD_CORES" -n 1 bash -c '
            set -o pipefail
            NANOFIL_CHECKS=reference NANOFIL_JOBS=1 tests/par.sh rocq/valid.sh "$0" 2>&1 \
              | tee "$TMPDIR/prog-$$.log" | grep --line-buffered "^@@nanofil-" \
              || { echo "### valid $0"; cat "$TMPDIR/prog-$$.log"; exit 1; }' <prog.list
          # Lua's whole-module mutant generation alone takes minutes on one
          # core. Once the other programs finish, share its independent item
          # partitions across the available cores, without nested matrix fanout.
          NANOFIL_CHECKS=reference NANOFIL_JOBS=1 NANOFIL_MUTANT_JOBS=$NIX_BUILD_CORES \
            tests/par.sh rocq/valid.sh lua.ir | tee "$TMPDIR/prog-lua.log"
          echo "valid tests/c/prog and lua.ir: $(($(wc -l <prog.list) + 1)) modules agree"
          mark validator-programs
          mkdir -p $out
          cp "$TMPDIR"/agree-*.log "$TMPDIR"/valid-*.log "$TMPDIR"/prog-*.log $out/
        ''
    )
  )
