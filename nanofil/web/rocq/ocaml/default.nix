# Build the OCaml dterm-rocq renderer (nanofil/web/rocq/ocaml/).
# Compiles the fixed-grammar Rocq parser and HTML drawer into a
# standalone native binary with no external OCaml libraries.
{ pkgs }:
pkgs.stdenv.mkDerivation {
  pname = "dterm-rocq";
  version = "0.1.0";
  src = pkgs.lib.fileset.toSource {
    root = ./.;
    fileset = pkgs.lib.fileset.unions [
      ./dune
      ./dune-project
      (pkgs.lib.fileset.fileFilter (f: f.hasExt "ml") ./.)
    ];
  };
  nativeBuildInputs = [
    pkgs.ocaml
    pkgs.dune_3
  ];
  buildPhase = ''
    runHook preBuild
    dune build --release ./main.exe
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    install -Dm755 _build/default/main.exe "$out/bin/dterm-rocq"
    runHook postInstall
  '';
}
