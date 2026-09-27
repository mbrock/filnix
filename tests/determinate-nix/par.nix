# builtins.parallel: start every top-level drvPath in the background, then
# collect them on the main thread. Returns a digest of the name -> drvPath map.
{
  nixpkgs,
  filter ? null,
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
  sel =
    if filter == null then
      names
    else
      builtins.filter (n: builtins.match filter n != null) names;
  drvs = lib.genAttrs sel (
    n:
    let
      r = builtins.tryEval (
        let
          v = pkgs.${n};
        in
        if lib.isDerivation v then v.drvPath else null
      );
    in
    if r.success then r.value else null
  );
  json = builtins.toJSON drvs;
in
builtins.parallel (builtins.attrValues drvs) {
  count = builtins.length sel;
  sha256 = builtins.hashString "sha256" json;
}
