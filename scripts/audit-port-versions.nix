# Evaluate the active declarations, rather than the historical patches.nix table.
{
  root,
  system ? "x86_64-linux",
}:
let
  flake = builtins.getFlake "git+file://${root}";
  pkgs = import flake.inputs.nixpkgs { inherit system; };
  filc = flake.legacyPackages.${system}.pkgsFilc;
  ports = import (builtins.toPath "${root}/ports.nix") {
    inherit pkgs;
    prev = filc;
    final = filc;
  };
  specs = builtins.listToAttrs (
    pkgs.lib.concatMap (
      item:
      if item ? pname then
        [
          {
            name = item.pname;
            value = item;
          }
        ]
      else
        pkgs.lib.mapAttrsToList (name: value: { inherit name value; }) item
    ) ports
  );
  record =
    name: spec:
    let
      custom = spec ? __customDrv;
      attrs = if custom then { } else spec.attrs pkgs.${name};
      nativeValue = pkgs.${name}.version or null;
      filcValue = filc.${name}.version or null;
      nativeVersion = if nativeValue == null then null else toString nativeValue;
      version = if filcValue == null then null else toString filcValue;
      value = {
        inherit
          name
          version
          nativeVersion
          custom
          ;
        pname = filc.${name}.pname or name;
        versionOverride = custom || attrs ? version;
        sourceOverride = custom || attrs ? src;
        patches = map toString (filc.${name}.patches or [ ]);
        comparison =
          if nativeVersion == null || version == null then
            "custom"
          else if version == nativeVersion then
            "same"
          else if pkgs.lib.versionOlder version nativeVersion then
            "older"
          else
            "newer";
      };
      result = builtins.tryEval (builtins.deepSeq value value);
    in
    if result.success then
      result.value
    else
      {
        inherit name;
        error = "evaluation failed";
      };
in
pkgs.lib.mapAttrsToList record specs
