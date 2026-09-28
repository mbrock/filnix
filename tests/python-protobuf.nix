# Fil-C Python's protobuf uses the pure-Python backend (the upb extension is
# not ported); round-trip protoc-generated messages through it.
{ pkgs, pkgsFilc }:
let
  python = pkgsFilc.python3.withPackages (ps: [ ps.protobuf ]);
in
pkgsFilc.runCommand "filc-python-protobuf-check" { } ''
  cp ${./protobuf.proto} protobuf.proto
  ${pkgs.protobuf}/bin/protoc --python_out=. protobuf.proto
  PYTHONPATH=. ${python}/bin/python3 ${./python-protobuf.py} | tee log
  grep -q '^ok: ' log
  touch $out
''
