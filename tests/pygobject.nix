{ pkgs, pkgsFilc }:
let
  python = pkgsFilc.python3.withPackages (ps: [ ps.pygobject3 ]);
in
pkgs.runCommand "filc-pygobject-runtime-check" { } ''
  ${python}/bin/python3 ${./pygobject.py}
  touch "$out"
''
