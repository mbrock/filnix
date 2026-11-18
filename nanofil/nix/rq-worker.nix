# This file builds the worker behind rq, the persistent Rocq proof session.
# The worker is a small OCaml program that links Rocq's parser and
# interpreter and keeps one session alive behind a Unix socket. It uses the
# Rocq, OCaml and findlib of rocq-packages.nix, so a session loads the same
# objects that one.sh compiles. The rq command builds it on first use.
{ pkgs }:
let
  rocq = import ./rocq-packages.nix { inherit pkgs; };
  ocamlPackages = rocq.rocq-core.ocamlPackages;
in
pkgs.stdenv.mkDerivation {
  pname = "rq-worker";
  version = "0";
  src = ../rocq/scripts/glibc-tools/rq/worker;
  nativeBuildInputs = [
    ocamlPackages.ocaml
    ocamlPackages.findlib
  ];
  buildInputs = [
    rocq.rocq-core
    ocamlPackages.yojson
  ];
  buildPhase = ''
    ocamlfind ocamlopt -linkpkg -linkall -package rocq-runtime.toplevel,yojson,str,unix \
      rq_worker.ml -o rq-worker
  '';
  installPhase = ''
    install -Dm755 rq-worker $out/bin/rq-worker
  '';
}
