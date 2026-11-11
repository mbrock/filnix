# The list-sum worked example (rocq/spikes, docs/logic.md): listsum.c
# proved never to panic through the program logic in theories
# (Logic.v). The hand-rolled and early Iris spikes that docs/logic.md
# compares it with were removed in November 2026. Off the main path:
# nothing else imports them, and the quick gate and CI do not build
# this; the program logic itself is in the model.
#
#   nix build -L .#checks.x86_64-linux.nanofil-logic-spikes
#
# It checks that ListSumCode.v is what nanofil makes of listsum.c, then
# compiles the spikes against the model's compiled theories (the
# nanofil-rocq model's objects), printing each file's time. Then parse.sh
# reads every spike sentence back (web/rocq), with its Iris fixture.
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
      ../rocq/scripts/gallina.pl
      ../rocq/spikes
      ../web/rocq/rocq_syntax.pl
      ../web/rocq/tests/parse.sh
      ../web/rocq/tests/reprint.pl
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
    cp -rp ${model.objects}/share/rocq/theories nanofil/rocq/
    chmod -R u+w nanofil
    cd nanofil
    patchShebangs bin rocq/spikes
    FILCC=${filcc}/bin/clang bash rocq/spikes/code.sh
    bash rocq/spikes/build.sh | tee timings.log
    bash web/rocq/tests/parse.sh rocq/spikes/*.v
    mkdir -p $out
    cp timings.log $out/
  ''
