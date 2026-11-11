# M2's gate (docs/lambda-anf.md, anf/lower/tests/run.sh): CertiRocq's
# standalone programs and the Gallina backend's Asm.v printer and
# Order.v sort go through CertiRocq's λANF (certirocq-anf.nix),
# AnfLower.v and `nanofil-backend compile-allocated`, are linked with
# the arena of anf/, and must print what the same programs extracted
# to OCaml print, with the default nursery and with a 256-word one
# under FUGC_SCRIBBLE=1 FUGC_VERIFY=1. $out/gate.log has the table of
# counts and times.
#
# Run it when you want it: it builds CertiRocq, which is not in the
# binary cache, so no workflow builds it and scripts/nanofil-checks
# skips it unless it is named.
#
#   nix build -L .#checks.x86_64-linux.nanofil-anf-lower
#
# The programs run with a 1 GB stack (direct-style recursion over
# 100k-element lists), so the builder's hard stack limit must allow it.
{ pkgs, filcc }:
let
  certirocq = import ./certirocq-anf.nix { inherit pkgs; };
  inherit (certirocq) coq ocamlPackages;
  src = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../anf
      ../rocq/theories
      ../rocq/backend
      ../tests/watch.py
    ];
  };
in
pkgs.runCommandCC "nanofil-anf-lower"
  {
    nativeBuildInputs = [
      coq.coq
      ocamlPackages.ocaml
      ocamlPackages.findlib
      pkgs.python3
    ];
    buildInputs = [
      certirocq
      ocamlPackages.zarith
    ];
  }
  ''
    set -o pipefail
    cp -r ${src} nanofil
    chmod -R u+w nanofil
    cd nanofil
    patchShebangs anf/lower/tests
    export ROCQPATH=${certirocq}/lib/coq/9.1/user-contrib''${COQPATH:+:$COQPATH}''${ROCQPATH:+:$ROCQPATH}
    unset COQPATH
    export OCAMLPATH=${certirocq}/lib/ocaml/4.14.4/site-lib''${OCAMLPATH:+:$OCAMLPATH}
    (ulimit -s 1048576) || { echo "the gate needs a 1 GB stack; this builder's hard limit is $(ulimit -Hs) KB"; exit 1; }
    export CERTIROCQ_SRC=${certirocq.src} FILCC=${filcc}/bin/clang ANF_WORK=$PWD/work
    python3 tests/watch.py --label anf-gate --warn-after 1200 --timeout 3600 -- \
      anf/lower/tests/run.sh | tee gate.log
    mkdir -p $out
    cp gate.log $out/
  ''
