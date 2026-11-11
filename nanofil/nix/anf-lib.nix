# libnanofil's gate (docs/lambda-anf.md, M4; anf/lib/run.sh): the
# Gallina backend through λANF, as anf-backend.nix builds it, linked
# into the Fil-C shared library libnanofil.so, and called in one process
# on every IR fixture for compile, compile-promoted and
# compile-allocated, three rounds over the library's one arena, with the
# default nursery and a 4096-word one under FUGC_SCRIBBLE=1
# FUGC_VERIFY=1; each compile must give what the OCaml build of the
# backend gives. $out has the gate's log and the library.
#
# Run it when you want it: it builds CertiRocq, which is not in the
# binary cache, and compiling the lowered backend takes about 5 minutes
# and 1.4 GB, so no workflow builds it.
#
#   nix build -L .#checks.x86_64-linux.nanofil-anf-lib
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
pkgs.runCommandCC "nanofil-anf-lib"
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
    patchShebangs anf/lib/run.sh
    export ROCQPATH=${certirocq}/lib/coq/9.1/user-contrib''${COQPATH:+:$COQPATH}''${ROCQPATH:+:$ROCQPATH}
    unset COQPATH
    export OCAMLPATH=${certirocq}/lib/ocaml/4.14.4/site-lib''${OCAMLPATH:+:$OCAMLPATH}
    export FILCC=${filcc}/bin/clang ANF_WORK=$PWD/work
    python3 tests/watch.py --label anf-lib --warn-after 1800 --timeout 5400 -- \
      anf/lib/run.sh | tee gate.log
    mkdir -p $out
    cp gate.log work/libnanofil.so anf/lib/nanofil.h $out/
  ''
