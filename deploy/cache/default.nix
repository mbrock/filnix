{
  pkgs ? import (builtins.fetchTree (builtins.fromJSON (
    builtins.readFile ../../flake.lock
  )).nodes.nixpkgs.locked) { },
}:
pkgs.writeShellApplication {
  name = "filnix-publish-cache";
  runtimeInputs = [
    pkgs.python3
    pkgs.cachix
  ];
  text = ''
    export PATH=/nix/var/nix/profiles/default/bin:$PATH
    exec python3 ${../../scripts/publish-cache.py} "$@"
  '';
}
