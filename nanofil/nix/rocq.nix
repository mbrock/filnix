# The Rocq model of the checked IR (rocq/, docs/formal.md Campaign 1):
# compile it with the pinned nixpkgs' Rocq, refuse any Admitted or Axiom
# (none is allowed outside the Campaign 2 runtime module type, which
# does not exist yet), extract and link the model, then check that it
# agrees with interp:run/5 on every run line of rocq/tests, the Fil-C
# IR fixtures, the C tests and Fil-C modules from tests/gen.pl, the
# last three with and without -O and under every --checks mode
# (rocq/agree.sh); and that its validator
# reaches ir:valid_module/1's verdict on mutants of every checked module
# in the same matrix, and of the tests/c/prog programs with aliases and
# weak, thread-local or constructor data (rocq/valid.sh).
{ pkgs, filcc }:
let
  rocq = pkgs.rocqPackages;
  ocamlPackages = rocq.rocq-core.ocamlPackages;
  model = pkgs.stdenv.mkDerivation {
    name = "nanofil-rocq-model";
    src = ../rocq;
    nativeBuildInputs = [
      rocq.rocq-core
      rocq.stdlib
      ocamlPackages.ocaml
      ocamlPackages.findlib
    ];
    buildInputs = [ ocamlPackages.zarith ];
    buildPhase = ''
      if grep -rnwE 'Admitted|Axiom|Axioms|Parameter|Conjecture' theories; then
        echo "rocq: no Admitted or Axiom outside the runtime module type" >&2
        exit 1
      fi
      make
    '';
    installPhase = ''
      mkdir -p $out/bin
      cp nanofil-model $out/bin/
    '';
  };
in
pkgs.runCommandCC "nanofil-rocq-check"
  {
    nativeBuildInputs = [ pkgs.swi-prolog ];
    passthru = { inherit model; };
  }
  ''
    cp -r ${../.} nanofil
    chmod -R u+w nanofil
    cd nanofil
    patchShebangs rocq bin
    export FILCC=${filcc}/bin/clang MODEL=${model}/bin/nanofil-model
    bin/nanofil --save-state "$TMPDIR/nanofil.state"
    export NANOFIL_STATE=$TMPDIR/nanofil.state
    # Hand-written checked IR (rocq/tests) goes in as written: the check
    # passes take pizlonate's output, never renew_hull or renew_if.
    NANOFIL_CHECKS=reference rocq/agree.sh rocq/tests/*.ir
    # Forty Fil-C modules of ten random functions (tests/gen.pl's filc
    # mode), which trap often, join the matrix below.
    mkdir gen
    for seed in $(seq 1 40); do
      (cd src && ../bin/nanofil --script ../tests/gen.pl $seed 10 filc </dev/null) > gen/gen-$seed.ir
    done
    for opt in "" -O; do
      for checks in reference reuse renew guard hoist schedule half forward combined hull getter extended; do
        echo "### NANOFIL_OPT=$opt NANOFIL_CHECKS=$checks"
        NANOFIL_OPT=$opt NANOFIL_CHECKS=$checks rocq/agree.sh tests/filc/*.ir tests/c/*.c gen/*.ir
      done
    done
    # The validator against ir:valid_module/1 on mutants of every checked
    # module (rocq/valid.sh, rocq/mutants.pl), in every mode at once.
    NANOFIL_CHECKS=reference rocq/valid.sh rocq/tests/*.ir
    # (xargs drops empty words, so "plain" stands for no -O.)
    for opt in plain -O; do
      for checks in reference reuse renew guard hoist schedule half forward combined hull getter extended; do
        echo "$opt $checks"
      done
    done | xargs -P "$NIX_BUILD_CORES" -L 1 sh -c '
      opt=$0; [ "$opt" = plain ] && opt=
      NANOFIL_OPT=$opt NANOFIL_CHECKS=$1 rocq/valid.sh tests/filc/*.ir tests/c/*.c gen/*.ir \
        >"$TMPDIR/valid-$0-$1.log" 2>&1 || { echo "### valid NANOFIL_OPT=$opt NANOFIL_CHECKS=$1"; cat "$TMPDIR/valid-$0-$1.log"; exit 1; }
      echo "valid NANOFIL_OPT=$opt NANOFIL_CHECKS=$1: $(grep -c "^/" "$TMPDIR/valid-$0-$1.log") files agree"'
    # The C programs of tests/c/prog that declare an alias, a weak
    # symbol, thread-local data or a constructor, with the reference
    # checks only: they bring the corpus's aliases and its kinds of data
    # linkage. Not those with a "// cflags:" line, which compile as
    # progtest.sh does and not as cc-ir does.
    grep -lE 'alias *\(|weak|_Thread_local|__thread|thread_local|constructor|destructor' \
      $(grep -L '^// cflags:' tests/c/prog/*.c) >prog.list
    xargs -P "$NIX_BUILD_CORES" -n 1 sh -c '
      NANOFIL_CHECKS=reference rocq/valid.sh "$0" >"$TMPDIR/prog-$$.log" 2>&1 \
        || { echo "### valid $0"; cat "$TMPDIR/prog-$$.log"; exit 1; }' <prog.list
    echo "valid tests/c/prog: $(wc -l <prog.list) programs agree"
    touch $out
  ''
