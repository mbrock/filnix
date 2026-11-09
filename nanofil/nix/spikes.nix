# The logic spikes (rocq/spikes, docs/logic.md): two small program
# logics proving the same program never panics, one hand-rolled and one
# on Iris. Off the main path: nothing else imports them, the quick gate
# and CI do not build this, and only this derivation depends on Iris.
#
#   nix build -L .#checks.x86_64-linux.nanofil-logic-spikes
#
# It checks that ListSumCode.v is what nanofil makes of listsum.c, then
# compiles the spikes against the model's compiled theories (the
# nanofil-rocq model output), printing each file's time.
{
  pkgs,
  filcc,
  model,
}:
let
  rocq = pkgs.rocqPackages;
  src = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../src
      ../bin
      ../rocq/gallina.pl
      ../rocq/spikes
    ];
  };
in
pkgs.runCommandCC "nanofil-logic-spikes"
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      pkgs.python3
      rocq.rocq-core
      rocq.stdlib
      rocq.stdpp
      rocq.iris
    ];
  }
  ''
    set -o pipefail
    cp -r ${src} nanofil
    chmod -R u+w nanofil
    cd nanofil
    patchShebangs bin rocq/spikes
    FILCC=${filcc}/bin/clang bash rocq/spikes/code.sh
    bash rocq/spikes/build.sh ${model}/share/rocq/theories | tee timings.log
    mkdir -p $out
    cp timings.log $out/
  ''
