# nanofil: unit tests, then the fixtures and a seeded random corpus run
# through the interpreter, qbe and nanofil's own backend. nanofil alone
# must also get the qbe-bugs repros right.
{ pkgs }:
let
  trealla = import ./trealla.nix { inherit pkgs; };
in
pkgs.runCommandCC "nanofil-check"
  {
    nativeBuildInputs = [
      trealla
      pkgs.qbe
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
    touch $out
  ''
