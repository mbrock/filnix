# CertiRocq (https://github.com/CertiCoq/certicoq), Rocq's verified
# compiler from Gallina through MetaRocq erasure and LambdaANF to
# CompCert Clight C. certirocq-anf.nix adds the λANF tap for the
# λANF lowering gate (docs/lambda-anf.md); it was first built for a C
# build of the Gallina backend (docs/gallina-backend.md, M8).
#
# Pinned to commit 943b52ae and patched (certirocq-nanofil.patch) so
# it builds against Rocq 9.1.1 and nixpkgs' cached MetaRocq 1.5.1-9.1
# without wasmcert or a full CompCert proof build:
#
# - CompCert: only the LGPL-2.1 Clight AST definitions CertiRocq's
#   codegen imports (export/Clightdefs.vo, cfrontend/Csyntax.vo,
#   common/Globalenvs.vo) are compiled (~38 s).
# - CertiRocq: theories/Compiler/pipeline.v uses MetaRocq 1.5.1's
#   Erasure.run_erase_program, cps.v restores the 1-line EAst.tBox
#   case, the unused Wasm backend is dropped, and the proof-only
#   sections at the bottom of hoisting.v and inline_letapp.v are
#   truncated so Extraction/extraction.vo builds without compiling
#   the logical-relations proof development.
{ pkgs }:
let
  coq = pkgs.coqPackages_9_1;
  ocamlPackages = coq.coq.ocamlPackages;
  compcert =
    (
      (import pkgs.path {
        system = pkgs.stdenv.hostPlatform.system;
        config.allowUnfree = true;
      }).coqPackages_9_1.compcert.overrideAttrs
        (old: {
          outputs = [
            "out"
            "lib"
          ];
          buildPhase = "make depend && make -j$NIX_BUILD_CORES export/Clightdefs.vo cfrontend/Csyntax.vo common/Globalenvs.vo";
          installPhase = "mkdir -p $out $lib/lib/coq/9.1/user-contrib/compcert; for d in lib common x86_64 x86 cfrontend export; do mkdir -p $lib/lib/coq/9.1/user-contrib/compcert/$d; cp -f $d/*.v $d/*.vo $d/*.glob $lib/lib/coq/9.1/user-contrib/compcert/$d/ 2>/dev/null || true; done";
        })
    ).lib;
in
pkgs.stdenv.mkDerivation {
  pname = "rocq-certirocq";
  version = "0-unstable-943b52a";
  src = pkgs.fetchFromGitHub {
    owner = "CertiCoq";
    repo = "certicoq";
    rev = "943b52ae654708130f241ccf8a50ecb95a7956e2";
    sha256 = "168vhwjj1fjppvr28dd2iwlinzkyfn55kxxd44dx4kp3fp59kzky";
  };
  patches = [ ./certirocq-nanofil.patch ];
  nativeBuildInputs = [
    coq.coq
    ocamlPackages.ocaml
    ocamlPackages.findlib
    pkgs.python3
    pkgs.rsync
    pkgs.which
  ];
  propagatedBuildInputs = [
    coq.stdlib
    coq.ExtLib
    coq.equations
    coq.metarocq
    coq.flocq
    coq.MenhirLib
    compcert
  ];
  postPatch = ''
    patchShebangs configure.sh clean_extraction.sh make_plugin.sh
    # Proof-only sections at the end of hoisting.v and inline_letapp.v
    # import logical_relations.v; truncating them lets extraction.vo
    # compile only the executable compiler pipeline.
    sed -i '105,$d' theories/LambdaANF/hoisting.v
    sed -i '53,$d' theories/LambdaANF/inline_letapp.v
    sed -i 's/LambdaANF\.logical_relations//g; s/logical_relations//g' \
      theories/LambdaANF/hoisting.v theories/LambdaANF/inline_letapp.v
  '';
  configurePhase = ''
    runHook preConfigure
    export COQPATH="${compcert}/lib/coq/9.1/user-contrib''${COQPATH:+:$COQPATH}"
    ./configure.sh local
    runHook postConfigure
  '';
  buildPhase = ''
    runHook preBuild
    export COQPATH="${compcert}/lib/coq/9.1/user-contrib''${COQPATH:+:$COQPATH}"
    (cd libraries && coq_makefile -f _CoqProject -o Makefile)
    make -C libraries -j "$NIX_BUILD_CORES"
    (cd theories && coq_makefile -f _CoqProject -o Makefile)
    make -C theories -j "$NIX_BUILD_CORES" Extraction/extraction.vo
    make -C runtime
    bash ./clean_extraction.sh plugins/plugin
    python3 plugins/manifests/generate.py plugin
    (cd plugins/plugin && coq_makefile -f _CoqProject -o Makefile)
    make -C plugins/plugin -j "$NIX_BUILD_CORES"
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$OCAMLFIND_DESTDIR" "$out/lib/coq/9.1/user-contrib"
    make -C plugins/plugin install \
      COQLIBINSTALL="$out/lib/coq/9.1/user-contrib" \
      COQPLUGININSTALL="$OCAMLFIND_DESTDIR" \
      COQDOCINSTALL="$out/share/coq/9.1/user-contrib"
    mkdir -p "$out/lib/coq/9.1/user-contrib/CertiRocq/Plugin/runtime"
    cp runtime/*.h runtime/*.c runtime/*.o \
      "$out/lib/coq/9.1/user-contrib/CertiRocq/Plugin/runtime/"
    (cd theories && find . -name '*.vo' -o -name '*.glob' | while read -r f; do
      install -D "$f" "$out/lib/coq/9.1/user-contrib/CertiRocq/$f"
    done)
    cp -r ${compcert}/lib/coq/9.1/user-contrib/compcert "$out/lib/coq/9.1/user-contrib/"
    runHook postInstall
  '';
  passthru = {
    inherit coq ocamlPackages compcert;
  };
}
