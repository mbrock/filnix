# The glibc spike (rocq/glibc, docs/glibc-ir.md): programs linked with
# nanofil's IR of user glibc units, proved through the program logic,
# with libpizlo's zsys_write as the one trusted contract. Off the main
# path: nothing else imports these files, and neither the quick gate
# nor CI builds this.
#
#   nix build -L .#checks.x86_64-linux.nanofil-glibc
#
# It compiles the proofs against the model's compiled theories (the
# nanofil-rocq model's objects), printing each file's time, reads every
# sentence back with parse.sh (web/rocq), and runs the native probe of
# the zsys_write contract with filcc. That the Code.v fixtures are
# nanofil's current products is rocq/glibc/code.sh's check, which needs
# the user glibc capture (survey/glibc/capture.nix) and is run by hand.
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
      ../rocq/glibc
      ../tests/watch.py
      ../web/rocq/rocq_syntax.pl
      ../web/rocq/tests/parse.sh
      ../web/rocq/tests/reprint.pl
    ];
  };
in
pkgs.runCommandCC "nanofil-glibc"
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
    patchShebangs rocq/glibc
    python3 tests/watch.py --label "glibc proofs" --warn-after 120 --timeout 600 -- \
      bash rocq/glibc/build.sh | tee timings.log
    python3 tests/watch.py --label "glibc parse" --warn-after 120 --timeout 600 -- \
      bash web/rocq/tests/parse.sh rocq/glibc/*.v
    FILCC=${filcc}/bin/clang bash rocq/glibc/probe.sh
    mkdir -p $out
    cp timings.log $out/
  ''
