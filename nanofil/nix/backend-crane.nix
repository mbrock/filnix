# The Gallina backend extracted to C++ by Crane (rocq/backend/crane,
# docs/gallina-backend.md, M6): the same Gallina as nix/backend.nix
# extracts to OCaml, held to the same Prolog output.
#
#   nix build -L .#checks.x86_64-linux.nanofil-backend-crane
#
# It builds the OCaml backend, for the model files and backend files
# the compiler imports and as the reference of the allocated compiler,
# extracts the compiler with Crane (nix/crane.nix) and compiles the
# C++ with clang, which is most of its time. Then:
#
# - the self-test: each stdlib function that CraneMap.v maps to C++
#   gives, on numbers at and past the machine's widths, what
#   vm_compute finds for it (CraneSelfTest.v, selftest.cpp);
# - `nanofil-backend-cpp compile` and `compile-promoted` print what
#   `nanofil compile` and `nanofil compile-promoted` print, byte for
#   byte, and refuse what they refuse (rocq/backend/tests/compile.sh),
#   on the IR fixtures; the files not taken are those
#   rocq/backend/tests/compile/none.txt names;
# - `nanofil-backend-cpp compile-allocated` prints what the OCaml
#   build's `compile-allocated` prints, byte for byte, and exits as it
#   does (rocq/backend/crane/tests/same.sh), on the same fixtures and
#   those of rocq/backend/tests/regs; Prolog has no such command, and
#   tests/regs.sh holds the OCaml build's output to how the programs
#   behave (nix/backend.nix);
# - parse.sh reads every sentence of the Crane files back (web/rocq).
#
# No Fil-C toolchain: the fixtures are IR text.
{ pkgs }:
let
  crane = import ./crane.nix { inherit pkgs; };
  inherit (crane) coq ocamlPackages;
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
pkgs.runCommandCC "nanofil-backend-crane"
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      pkgs.python3
      coq.coq
      coq.stdlib
      ocamlPackages.ocaml
      ocamlPackages.findlib
      pkgs.llvmPackages_20.clang
    ];
    buildInputs = [
      pkgs.gmpxx
      ocamlPackages.zarith
    ];
  }
  ''
    set -o pipefail
    cp -r ${src} nanofil
    chmod -R u+w nanofil
    cd nanofil
    patchShebangs bin tests rocq/backend
    # nixpkgs' coq names its libraries in COQPATH, which Rocq 9.1 warns
    # about at every start.
    export ROCQPATH=${crane}/lib/coq/9.1/user-contrib''${COQPATH:+:$COQPATH}''${ROCQPATH:+:$ROCQPATH}
    unset COQPATH
    export OCAMLPATH=${crane}/lib/ocaml/site-lib''${OCAMLPATH:+:$OCAMLPATH}
    make -C rocq/backend -j"$NIX_BUILD_CORES" | tee timings.log
    python3 tests/watch.py --label "extract and compile the C++" --warn-after 600 --timeout 1500 -- \
      make -C rocq/backend/crane -j"$NIX_BUILD_CORES" check CRANE_INCLUDE=${crane}/include | tee crane.log
    export NANOFIL_JOBS=$NIX_BUILD_CORES BACKEND=$PWD/rocq/backend/crane/nanofil-backend-cpp
    bin/nanofil --save-state "$TMPDIR/nanofil.state"
    export NANOFIL_STATE=$TMPDIR/nanofil.state
    tests/par.sh rocq/backend/tests/compile.sh ${fixtures} | tee compile.log
    COMMAND=compile-promoted tests/par.sh rocq/backend/tests/compile.sh ${fixtures} | tee compile-promoted.log
    REFERENCE=$PWD/rocq/backend/nanofil-backend tests/par.sh rocq/backend/crane/tests/same.sh \
      ${fixtures} rocq/backend/tests/regs/*.ir | tee compile-allocated.log
    # Reprinting CraneExtract.v extracts once more.
    PARSE_IN_PLACE=1 python3 tests/watch.py --label "crane parse/typecheck" --warn-after 300 --timeout 900 -- \
      bash web/rocq/tests/parse.sh rocq/backend/crane/*.v
    mkdir -p $out/bin
    cp rocq/backend/crane/nanofil-backend-cpp $out/bin/
    cp timings.log crane.log compile.log compile-promoted.log compile-allocated.log $out/
  ''
