# Cache prover execution independently of the presentation assets.
# With spikes, the logic spikes' states (rocq/spikes), replayed against
# the theories they import.
{
  pkgs,
  spikes ? false,
}:
let
  rocq = import ../../nix/rocq-packages.nix { inherit pkgs; };
  # The capture client uses the Coq command shims and the RocqIDE XML server.
  coq =
    (pkgs.coq_9_2.override {
      coq-version = rocq.rocq-core.rocq-version;
      rocqPackages = rocq;
    }).overrideAttrs
      {
        inherit (rocq.rocq-core) version src;
      };
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
        # rocq_draw.pl and dterm_rocq.pl load it, for the capture regression.
        ../concepts.pl
        ./tests/capture.py
      ]
      ++ pkgs.lib.optional spikes ../../rocq/spikes
    );
  };
in
pkgs.runCommand
  (if spikes then "dterm-rocq-spike-states" else "dterm-rocq-proof-states")
  {
    # The theories' program logic (Heap.v, Language.v, Logic.v) and the
    # spikes both need std++ and Iris.
    nativeBuildInputs = [
      coq
      rocq.stdlib
      rocq.stdpp
      rocq.iris
      rocq.rocq-core.ocamlPackages.ocaml
      rocq.rocq-core.ocamlPackages.findlib
      pkgs.stdenv.cc
      pkgs.swi-prolog
      pkgs.python3
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
        # Every theory is compiled and replayed: minutes, growing with the
        # development, so the budgets are check.nix's, not watch.py's
        # five-minute default meant for single steps.
        python3 ${src}/nanofil/tests/watch.py --label "Rocq proof-state capture" \
          --warn-after 300 --timeout 1800 -- \
          python3 ${src}/nanofil/web/rocq/capture.py project $out
      ''
  )
