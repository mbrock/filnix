# Cache prover execution independently of the presentation assets.
# With spikes, the logic spikes' states (rocq/spikes, which need std++
# and Iris), replayed against the theories they import.
{
  pkgs,
  spikes ? false,
}:
let
  src = pkgs.lib.fileset.toSource {
    root = ../../..;
    fileset = pkgs.lib.fileset.unions (
      [
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
      ]
      ++ pkgs.lib.optional spikes ../../rocq/spikes
    );
  };
in
pkgs.runCommand
  (if spikes then "dterm-rocq-spike-states" else "dterm-rocq-proof-states")
  {
    nativeBuildInputs = [
      pkgs.coq
      pkgs.coqPackages.stdlib
      pkgs.swi-prolog
      pkgs.python3
    ]
    ++ pkgs.lib.optionals spikes [
      pkgs.rocqPackages.stdpp
      pkgs.rocqPackages.iris
    ];
  }
  (
    if spikes then
      ''
        mkdir project
        cp -r ${src}/nanofil/rocq/. project/
        chmod -R u+w project
        # One project: the theories as Nanofil, the spikes as Spike.
        echo "-R spikes Spike" >>project/_RocqProject
        grep '\.v$' project/spikes/_RocqProject | sed 's#^#spikes/#' >>project/_RocqProject
        python3 ${src}/nanofil/tests/watch.py --label "Spike proof-state capture" -- \
          python3 ${src}/nanofil/web/rocq/capture.py project $out --replay spikes/
      ''
    else
      ''
        python3 ${src}/nanofil/tests/watch.py --label "Proof capture regression" -- \
          python3 ${src}/nanofil/web/rocq/tests/capture.py
        mkdir -p project/extraction
        cp -r ${src}/nanofil/rocq/. project/
        chmod -R u+w project
        python3 ${src}/nanofil/tests/watch.py --label "Rocq proof-state capture" -- \
          python3 ${src}/nanofil/web/rocq/capture.py project $out
      ''
  )
