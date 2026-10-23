# nanofil: unit tests, then the fixtures and a seeded random corpus run
# through the interpreter, qbe and nanofil's own backend. nanofil alone
# must also get the qbe-bugs repros right. Fil-C modules (tests/filc) are
# linked with clang-built Fil-C code and run natively; the GC test also
# runs with FUGC_SCRIBBLE and FUGC_VERIFY, which a missed root or store
# barrier needs to show up. C files (tests/c) are compiled by nanofil and
# by clang and both run against the interpreter; tests/c/reject must be
# refused with the expected messages. Whole programs (tests/c/prog) are
# built by nanofil and by clang and must print and exit the same, also
# under FUGC_SCRIBBLE and FUGC_VERIFY.
{ pkgs, filcc }:
let
  trealla = import ./trealla.nix { inherit pkgs; };
  qbe = import ./qbe.nix { inherit pkgs; };
in
pkgs.runCommandCC "nanofil-check"
  {
    nativeBuildInputs = [
      trealla
      qbe
      pkgs.python3
    ];
  }
  ''
    cp -r ${../.} nanofil
    chmod -R u+w nanofil
    cd nanofil
    patchShebangs tests
    (cd src && tpl -q ../tests/unit.pl </dev/null) | tee unit.log
    grep -q 'tests ok$' unit.log
    python3 -I tests/gen.py 1 200 > gen1.ssa
    CC=$CC tests/difftest.sh tests/fixtures/*.ssa gen1.ssa
    CC=$CC VARIANTS=nanofil tests/difftest.sh tests/qbe-bugs/*.ssa
    export FILCC=${filcc}/bin/clang
    tests/difftest.sh tests/filc/basic.ssa tests/filc/globals.ssa
    tests/filc/run-c.sh interop gc
    tests/difftest.sh tests/c/*.c
    tests/reject.sh
    tests/progtest.sh
    RUN_ENV="env FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/progtest.sh
    RUN_ENV="FUGC_SCRIBBLE=1 FUGC_VERIFY=1" tests/filc/run-c.sh gc
    touch $out
  ''
