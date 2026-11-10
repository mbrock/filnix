# The Gallina backend (rocq/backend, docs/gallina-backend.md): the
# compiler's middle and back end in Gallina, extracted to OCaml and
# held to the Prolog compiler's output byte for byte. Off the quick
# Rocq gate: nothing in the model imports it.
#
#   nix build -L .#checks.x86_64-linux.nanofil-backend
#   nix build -L .#checks.x86_64-linux.nanofil-backend-full
#
# It compiles the backend and the model files it imports (theories;
# not the model's proofs, so this does not wait for them), printing
# each file's time, extracts and links bin/nanofil-backend, and runs
# the gates of the milestones reached so far. M1: the extracted
# printer prints asm.pl's text from the lines the Prolog compiler
# emits (rocq/backend/tests/asm.sh), on the Fil-C IR fixtures and
# seven C programs that between them reach every line form; full=true
# takes the whole corpus, with and without -O. M2: the extracted ABI
# plans are the terms filc_abi.pl prints (rocq/backend/tests/abi.sh),
# on the same files and six more C programs that reach the plan forms
# the others lack; full=true takes the whole corpus. NFB: Nfb.v's
# writer writes the words nfb.pl writes and its reader reads them back
# (rocq/backend/tests/nfb.sh, docs/nfb.md), on the same files; full=true
# takes the whole corpus, with and without -O. M3: the lines the
# backend gives each function's plan, each data item, alias and weak
# thunk are the reference emission's, and without -O the whole
# module's text is `nanofil compile`'s wherever every function is in
# the subset (rocq/backend/tests/emit.sh), on the same files and the
# fixtures of rocq/backend/tests/edge, which reach the arms the corpus
# does not; full=true takes the whole corpus, with and without -O.
# Then parse.sh reads every backend sentence back (web/rocq).
{
  pkgs,
  filcc,
  full ? false,
}:
let
  rocq = pkgs.rocqPackages;
  ocamlPackages = rocq.rocq-core.ocamlPackages;
  src = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../src
      ../bin
      ../tests
      ../rocq/theories
      ../rocq/backend
      ../web/rocq/rocq_syntax.pl
      ../web/rocq/tests/parse.sh
      ../web/rocq/tests/reprint.pl
    ];
  };
  quick = "tests/filc/*.ir tests/c/ldouble.c tests/c/prog/address-difference.c tests/c/prog/alias.c tests/c/prog/asm-fixed.c tests/c/prog/constructor.c tests/c/prog/source-bytes.c tests/c/prog/thread-local.c";
  quickAbi = "${quick} tests/c/fstructs.c tests/c/variadic.c tests/c/prog/structs.c tests/c/prog/memcpy-small.c tests/c/prog/weak-symbols.c tests/c/prog/byval.c";
  corpus = "tests/filc/*.ir tests/c/*.c tests/c/prog/*.c";
  edge = "rocq/backend/tests/edge/*.ir";
in
pkgs.runCommandCC (if full then "nanofil-backend-full" else "nanofil-backend")
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
  (
    ''
      set -o pipefail
      cp -r ${src} nanofil
      chmod -R u+w nanofil
      cd nanofil
      patchShebangs bin tests rocq/backend
      make -C rocq/backend -j"$NIX_BUILD_CORES" | tee timings.log
      export FILCC=${filcc}/bin/clang NANOFIL_JOBS=$NIX_BUILD_CORES
      bin/nanofil --save-state "$TMPDIR/nanofil.state"
      export NANOFIL_STATE=$TMPDIR/nanofil.state
    ''
    + (
      if full then
        ''
          tests/par.sh rocq/backend/tests/asm.sh ${corpus} | tee asm.log
          NANOFIL_OPT=-O tests/par.sh rocq/backend/tests/asm.sh ${corpus} | tee asm-O.log
          tests/par.sh rocq/backend/tests/abi.sh ${corpus} | tee abi.log
          tests/par.sh rocq/backend/tests/nfb.sh ${corpus} | tee nfb.log
          NANOFIL_OPT=-O tests/par.sh rocq/backend/tests/nfb.sh ${corpus} | tee nfb-O.log
          tests/par.sh rocq/backend/tests/emit.sh ${corpus} ${edge} | tee emit.log
          NANOFIL_OPT=-O tests/par.sh rocq/backend/tests/emit.sh ${corpus} ${edge} | tee emit-O.log
        ''
      else
        ''
          tests/par.sh rocq/backend/tests/asm.sh ${quick} | tee asm.log
          tests/par.sh rocq/backend/tests/abi.sh ${quickAbi} | tee abi.log
          tests/par.sh rocq/backend/tests/nfb.sh ${quickAbi} | tee nfb.log
          tests/par.sh rocq/backend/tests/emit.sh ${quickAbi} ${edge} | tee emit.log
        ''
    )
    + ''
      python3 tests/watch.py --label "backend parse/typecheck" -- bash web/rocq/tests/parse.sh rocq/backend/*.v
      mkdir -p $out/bin
      cp rocq/backend/nanofil-backend $out/bin/
      cp timings.log asm*.log abi.log nfb*.log emit*.log $out/
    ''
  )
