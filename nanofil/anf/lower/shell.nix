# The environment of M2's gate (tests/run.sh, docs/lambda-anf.md):
# Rocq 9.1.1 with CertiRocq and its λANF tap (nix/certirocq-anf.nix),
# OCaml with findlib and zarith, and CERTIROCQ_SRC for its tests/lib.
#
#   nix-shell nanofil/anf/lower/shell.nix
{
  pkgs ? import (builtins.getFlake (toString ../../..)).inputs.nixpkgs {
    system = "x86_64-linux";
  },
}:
let
  certirocq = import ../../nix/certirocq-anf.nix { inherit pkgs; };
  inherit (certirocq) coq ocamlPackages;
in
pkgs.mkShell {
  packages = [
    coq.coq
    certirocq
    ocamlPackages.ocaml
    ocamlPackages.findlib
    ocamlPackages.zarith
    pkgs.python3
  ];
  CERTIROCQ_SRC = certirocq.src;
}
