# Cache prover execution independently of the presentation assets.
{ pkgs }:
let
  src = pkgs.lib.fileset.toSource {
    root = ../../..;
    fileset = pkgs.lib.fileset.unions [
      ../../rocq/_RocqProject
      ../../rocq/theories
      ../../tests/watch.py
      ./capture.py
      ./capture_plan.pl
      ./rocq_syntax.pl
      ./rocq_draw.pl
      ./dterm_rocq.pl
      ../dterm_html.pl
      ./tests/capture.py
    ];
  };
in
pkgs.runCommand "dterm-rocq-proof-states"
  {
    nativeBuildInputs = [
      pkgs.coq
      pkgs.coqPackages.stdlib
      pkgs.swi-prolog
      pkgs.python3
    ];
  }
  ''
    python3 ${src}/nanofil/tests/watch.py --label "Proof capture regression" -- \
      python3 ${src}/nanofil/web/rocq/tests/capture.py
    mkdir -p project/extraction
    cp -r ${src}/nanofil/rocq/. project/
    chmod -R u+w project
    python3 ${src}/nanofil/tests/watch.py --label "Rocq proof-state capture" -- \
      python3 ${src}/nanofil/web/rocq/capture.py project $out
  ''
