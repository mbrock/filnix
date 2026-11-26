# The Gallina C frontend (rocq/frontend: CLex, CParse, CCanon, CPp) through
# CertiRocq's λANF (certirocq-anf.nix), AnfLower.v, and
# `nanofil-backend compile-allocated`, linked with the arena of anf/ and
# Fil-C, and checked byte-for-byte against the OCaml extraction across every
# C test fixture and all 20 Fil-C glibc system headers under both default and
# 4096-word stress nurseries with FUGC verification.
#
# Opt-in like nanofil-anf-backend: builds CertiRocq, which is not in the
# binary cache.
#
#   nix build -L .#checks.x86_64-linux.nanofil-anf-frontend
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
      ../rocq/frontend
      ../tests
    ];
  };
in
pkgs.runCommandCC "nanofil-anf-frontend"
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
    patchShebangs anf/frontend/run.sh
    export ROCQPATH=${certirocq}/lib/coq/9.1/user-contrib''${COQPATH:+:$COQPATH}''${ROCQPATH:+:$ROCQPATH}
    unset COQPATH
    export OCAMLPATH=${certirocq}/lib/ocaml/4.14.4/site-lib''${OCAMLPATH:+:$OCAMLPATH}
    (ulimit -s 1048576) || { echo "the gate needs a 1 GB stack; this builder's hard limit is $(ulimit -Hs) KB"; exit 1; }
    export FILCC=${filcc}/bin/clang ANF_WORK=$PWD/work
    python3 tests/watch.py --label anf-frontend --warn-after 600 --timeout 1800 -- \
      anf/frontend/run.sh | tee gate.log
    mkdir -p $out/bin
    cp gate.log $out/
    cp work/anf-frontend $out/bin/
  ''
