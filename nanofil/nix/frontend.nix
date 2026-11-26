# The Gallina C frontend (rocq/frontend): CLex.v, CAttrs.v, CParse.v,
# CCanon.v, CPp.v, CIeee.v, and CTypes (CTypeAst.v, CTypeTables.v,
# CTypes.v, CTypeCanon.v) extracted to OCaml and held byte-for-byte to
# SWI-Prolog's c_lex.pl + c_parse.pl + c_pp.pl + ieee.pl + c_types.pl
# across every C test fixture, C23 fixture, preprocessor torture suite,
# IEEE 754 corpus, and typechecker corpus, plus a parse.sh grammar
# round-trip check over every frontend .v file.
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
    python3 tests/watch.py --label "frontend diff" -- \
      bash rocq/frontend/tests/diff.sh | tee diff.log
    python3 tests/watch.py --label "frontend parse/typecheck" -- \
      bash web/rocq/tests/parse.sh rocq/frontend/*.v | tee parse.log
    mkdir -p $out/bin
    cp rocq/frontend/nanofil-frontend $out/bin/
    cp build.log diff.log parse.log $out/
  ''
