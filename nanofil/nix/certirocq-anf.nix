# CertiRocq (certirocq.nix) with nanofil's λANF tap
# (docs/lambda-anf.md, M2): `CertiRocq Show IR` writes the program's
# λANF after the whole λANF pipeline (closure conversion, hoisting,
# dead-parameter elimination and duplicate merging included) as the
# Prolog clauses anf/lower/AnfLower.v reads, instead of upstream's
# pretty-printed text (certirocq-anf-tap.patch, Compiler/pipeline.v).
#
# The CompCert library is not propagated: certirocq.nix installs a
# copy of it in $out, and two copies make `Require compcert.lib.X`
# ambiguous for a program that imports CompCert itself.
{ pkgs }:
let
  certirocq = import ./certirocq.nix { inherit pkgs; };
in
certirocq.overrideAttrs (old: {
  pname = "rocq-certirocq-anf";
  patches = old.patches ++ [ ./certirocq-anf-tap.patch ];
  propagatedBuildInputs = builtins.filter (
    p: p != old.passthru.compcert
  ) old.propagatedBuildInputs;
})
