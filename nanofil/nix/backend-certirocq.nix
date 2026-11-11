# The Gallina backend compiled to C by CertiRocq (rocq/backend/certirocq,
# docs/gallina-backend.md, M8): the same Gallina as nix/backend.nix
# extracts to OCaml, held to the same Prolog and OCaml output.
#
#   nix build -L --impure --expr \
#     'import ./nanofil/nix/backend-certirocq.nix { pkgs = import (builtins.getFlake (toString ./.)).inputs.nixpkgs { system = "x86_64-linux"; }; }'
{ pkgs }:
let
  certirocq = import ./certirocq.nix { inherit pkgs; };
  inherit (certirocq) coq ocamlPackages;
  src = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../src
      ../bin
      ../tests/par.sh
      ../tests/watch.py
      ../tests/filc
      ../rocq/theories
      ../rocq/backend
      ../web/rocq/rocq_syntax.pl
      ../web/rocq/tests/parse.sh
      ../web/rocq/tests/reprint.pl
    ];
  };
  fixtures = "tests/filc/*.ir rocq/backend/tests/edge/*.ir rocq/backend/tests/pizlonate/*.ir rocq/backend/tests/compile/*.ir rocq/backend/tests/promote/*.ir";
in
pkgs.runCommandCC "nanofil-backend-certirocq"
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      pkgs.python3
      coq.coq
      ocamlPackages.ocaml
      ocamlPackages.findlib
      pkgs.llvmPackages_20.clang
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
    patchShebangs bin tests rocq/backend
    export ROCQPATH=${certirocq}/lib/coq/9.1/user-contrib''${COQPATH:+:$COQPATH}''${ROCQPATH:+:$ROCQPATH}
    unset COQPATH
    export OCAMLPATH=${certirocq}/lib/ocaml/4.14.4/site-lib''${OCAMLPATH:+:$OCAMLPATH}
    make -C rocq/backend -j"$NIX_BUILD_CORES" | tee timings.log
    python3 tests/watch.py --label "compile to C with CertiRocq and build C" --warn-after 300 --timeout 900 -- \
      make -C rocq/backend/certirocq -j"$NIX_BUILD_CORES" \
        CERTIROCQ_RUNTIME=${certirocq}/lib/coq/9.1/user-contrib/CertiRocq/Plugin/runtime | tee certirocq.log
    export NANOFIL_JOBS=$NIX_BUILD_CORES BACKEND=$PWD/rocq/backend/certirocq/nanofil-backend-c
    bin/nanofil --save-state "$TMPDIR/nanofil.state"
    export NANOFIL_STATE=$TMPDIR/nanofil.state
    tests/par.sh rocq/backend/tests/compile.sh ${fixtures} | tee compile.log
    COMMAND=compile-promoted tests/par.sh rocq/backend/tests/compile.sh ${fixtures} | tee compile-promoted.log
    REFERENCE=$PWD/rocq/backend/nanofil-backend tests/par.sh rocq/backend/crane/tests/same.sh \
      ${fixtures} rocq/backend/tests/regs/*.ir | tee compile-allocated.log
    mkdir -p $out/bin
    cp rocq/backend/certirocq/nanofil-backend-c $out/bin/
    cp timings.log certirocq.log compile.log compile-promoted.log compile-allocated.log $out/
  ''
