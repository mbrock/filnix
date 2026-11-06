# The Rocq model of the checked IR (rocq/, docs/formal.md Campaign 1):
# compile it with the pinned nixpkgs' Rocq, refuse any Admitted or Axiom
# (none is allowed outside the Campaign 2 runtime module type, which
# does not exist yet), extract and link the model, then check that it
# agrees with interp:run/5 on every run line of rocq/tests, the Fil-C
# IR fixtures and the C tests, the last two with and without -O and
# under every --checks mode (rocq/agree.sh).
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
    for opt in "" -O; do
      for checks in reference reuse renew guard hoist schedule half forward combined hull getter extended; do
        echo "### NANOFIL_OPT=$opt NANOFIL_CHECKS=$checks"
        NANOFIL_OPT=$opt NANOFIL_CHECKS=$checks rocq/agree.sh tests/filc/*.ir tests/c/*.c
      done
    done
    touch $out
  ''
