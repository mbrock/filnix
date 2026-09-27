# Every top-level derivation's drvPath (null when it fails to evaluate).
{ nixpkgs, filter ? null }:
let
  pkgs = import nixpkgs { system = "x86_64-linux"; config = { allowAliases = false; }; overlays = [ ]; };
  lib = pkgs.lib;
  names = builtins.attrNames pkgs;
  sel = if filter == null then names else builtins.filter (n: builtins.match filter n != null) names;
in
lib.genAttrs sel (n:
  let r = builtins.tryEval (let v = pkgs.${n}; in if lib.isDerivation v then v.drvPath else null);
  in if r.success then r.value else null)
