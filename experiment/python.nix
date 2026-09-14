{
  pkgs ? import (builtins.fetchTree (builtins.fromJSON (
    builtins.readFile ../flake.lock
  )).nodes.nixpkgs.locked) { },
  testing ? false,
}:
pkgs.python3.withPackages (
  ps:
  let
    tagflow = ps.buildPythonPackage {
      pname = "tagflow";
      version = "0.14.0-aa07b0d";
      pyproject = true;
      src = pkgs.fetchFromGitHub {
        owner = "lessrest";
        repo = "tagflow";
        rev = "aa07b0d7eec0b72a5dbc6a8d0ee1098c68b74d09";
        hash = "sha256-YF1Mc9MZ5lIJTVwXEaC0i+cs1EO50aD2DhwshdQRklE=";
      };
      build-system = [ ps.hatchling ];
      dependencies = [
        ps.anyio
        ps.beautifulsoup4
        ps.starlette
      ];
      pythonImportsCheck = [
        "tagflow"
        "tagflow.htmx"
        "tagflow.responses"
      ];
      doCheck = false;
    };
  in
  [
    tagflow
    ps.starlette
    ps.hypercorn
    ps.waitress
  ]
  ++ pkgs.lib.optionals testing [ ps.httpx ]
)
