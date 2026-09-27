# drvs.nix, restricted to names whose index is k modulo n (to bound memory).
{
  nixpkgs,
  n,
  k,
}:
let
  pkgs = import nixpkgs {
    system = "x86_64-linux";
    config = {
      allowAliases = false;
    };
    overlays = [ ];
  };
  lib = pkgs.lib;
  names = builtins.attrNames pkgs;
  sel = lib.filter (x: x != null) (
    lib.imap0 (i: name: if lib.mod i n == k then name else null) names
  );
in
lib.genAttrs sel (
  name:
  let
    r = builtins.tryEval (
      let
        v = pkgs.${name};
      in
      if lib.isDerivation v then v.drvPath else null
    );
  in
  if r.success then r.value else null
)
