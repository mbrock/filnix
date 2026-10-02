{
  pkgs ? import (builtins.fetchTree (builtins.fromJSON (
    builtins.readFile ../../flake.lock
  )).nodes.nixpkgs.locked) { },
}:
let
  python = pkgs.python3.withPackages (ps: [
    ps.pyarrow
    ps.boto3
    ps.duckdb
  ]);
  source = builtins.path {
    path = ../../experiment;
    name = "filnix-analytics-source";
    filter = path: type: builtins.baseNameOf path != "__pycache__";
  };
in
pkgs.runCommand "filnix-analytics-0.1.0" { passthru = { inherit python; }; }
  ''
    mkdir -p $out/lib/experiment $out/bin
    cp ${source}/*.py $out/lib/experiment/
    cat > $out/bin/filnix-analytics <<EOF
    #!${pkgs.runtimeShell}
    export PYTHONPATH=$out/lib
    exec ${python}/bin/python -P -m experiment.analytics "\$@"
    EOF
    chmod +x $out/bin/filnix-analytics
  ''
