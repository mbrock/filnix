{
  pkgs ? import (builtins.fetchTree (builtins.fromJSON (
    builtins.readFile ../flake.lock
  )).nodes.nixpkgs.locked) { },
}:
let
  python = pkgs.python3.withPackages (ps: [ ps.waitress ]);
  source = builtins.path {
    path = ./.;
    name = "filnix-experiment-source";
    filter = path: type: builtins.baseNameOf path != "__pycache__";
  };
in
pkgs.runCommand "filnix-experiment-0.12.6" { } ''
  mkdir -p $out/lib/experiment $out/bin
  cp -r ${source}/* $out/lib/experiment/
  cat > $out/bin/filnix-experiment <<EOF
  #!${pkgs.runtimeShell}
  export PYTHONPATH=$out/lib
  export FILNIX_NIX=/nix/var/nix/profiles/default/bin/nix
  exec ${python}/bin/python -P -m experiment "\$@"
  EOF
  chmod +x $out/bin/filnix-experiment
  cat > $out/bin/filnix-attempt <<EOF
  #!${pkgs.runtimeShell}
  export PYTHONPATH=$out/lib
  export FILNIX_NIX=/nix/var/nix/profiles/default/bin/nix
  exec ${python}/bin/python -P -m experiment.attempt "\$@"
  EOF
  chmod +x $out/bin/filnix-attempt
''
