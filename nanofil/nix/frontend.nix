# The Gallina C frontend, lowering passes (rocq/frontend), and unchecked-IR
# middle-end optimizer plus its soundness proof suite (rocq/opt): extracted to
# OCaml and held byte-for-byte to SWI-Prolog across every C test fixture, C23
# fixture, preprocessor torture suite, IEEE 754 corpus, typechecker corpus, IR
# lowering corpus, record-layout corpus, and optimizer suite, with zero-axiom
# Print Assumptions verification on rocq/opt/*Proof.v and a parse.sh grammar
# round-trip check over every rocq/opt and rocq/frontend .v file.
#
#   nix build -L .#checks.x86_64-linux.nanofil-frontend
{ pkgs }:
let
  rocq = pkgs.rocqPackages;
  ocamlPackages = rocq.rocq-core.ocamlPackages;
  src = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../src
      ../tests
      ../rocq/theories
      ../rocq/backend
      ../rocq/opt
      ../rocq/frontend
      ../web/rocq/rocq_syntax.pl
      ../web/rocq/tests/parse.sh
      ../web/rocq/tests/reprint.pl
    ];
  };
in
pkgs.runCommandCC "nanofil-frontend"
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      pkgs.python3
      rocq.rocq-core
      rocq.stdlib
      ocamlPackages.ocaml
      ocamlPackages.findlib
    ];
    buildInputs = [ ocamlPackages.zarith ];
  }
  ''
    set -o pipefail
    cp -r ${src} nanofil
    chmod -R u+w nanofil
    cd nanofil
    patchShebangs tests rocq/frontend/tests web/rocq/tests
    make -C rocq/frontend -j"$NIX_BUILD_CORES" | tee build.log
    make -C rocq/opt proofs -j"$NIX_BUILD_CORES" | tee opt-proofs.log
    python3 tests/watch.py --label "frontend diff" -- \
      bash rocq/frontend/tests/diff.sh | tee diff.log
    python3 tests/watch.py --label "frontend parse/typecheck" -- \
      bash web/rocq/tests/parse.sh rocq/opt/*.v rocq/frontend/*.v | tee parse.log
    mkdir -p $out/bin
    cp rocq/frontend/nanofil-frontend $out/bin/
    cp build.log opt-proofs.log diff.log parse.log $out/
  ''
