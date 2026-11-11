# M3's gate (docs/lambda-anf.md, anf/backend/run.sh): the Gallina
# backend's reader and three compilers, driven by anf/backend/Drive.v,
# go through CertiRocq's λANF (certirocq-anf.nix), AnfLower.v and
# `nanofil-backend compile-allocated`, are linked with the arena of
# anf/, and must print what the OCaml build of the backend prints on
# every IR fixture for compile, compile-promoted and compile-allocated,
# with the default nursery and with a 4096-word one under
# FUGC_SCRIBBLE=1 FUGC_VERIFY=1. $out/gate.log has the counts.
#
# Run it when you want it: it builds CertiRocq, which is not in the
# binary cache, and compiling the lowered backend (64 MB of IR) takes
# about 5 minutes and 1.4 GB, so no workflow builds it.
#
#   nix build -L .#checks.x86_64-linux.nanofil-anf-backend
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
      ../tests/filc
      ../tests/watch.py
    ];
  };
in
pkgs.runCommandCC "nanofil-anf-backend"
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
    patchShebangs anf/backend/run.sh
    export ROCQPATH=${certirocq}/lib/coq/9.1/user-contrib''${COQPATH:+:$COQPATH}''${ROCQPATH:+:$ROCQPATH}
    unset COQPATH
    export OCAMLPATH=${certirocq}/lib/ocaml/4.14.4/site-lib''${OCAMLPATH:+:$OCAMLPATH}
    (ulimit -s 1048576) || { echo "the gate needs a 1 GB stack; this builder's hard limit is $(ulimit -Hs) KB"; exit 1; }
    export FILCC=${filcc}/bin/clang ANF_WORK=$PWD/work
    python3 tests/watch.py --label anf-backend --warn-after 1800 --timeout 5400 -- \
      anf/backend/run.sh | tee gate.log
    mkdir -p $out
    cp gate.log $out/
  ''
