# Evaluate only: creates an immutable manifest with references to the source
# and derivations, not their realised outputs. No package builds are requested.
{
  source,
  revision,
  scope ? "world",
}:
let
  flake = builtins.getFlake source;
  packages = flake.legacyPackages.x86_64-linux.pkgsFilc;
  pkgs = import flake.inputs.nixpkgs { system = "x86_64-linux"; };
  world = import "${flake.outPath}/shells/world-packages.nix";
  declarations = import "${flake.outPath}/ports.nix" {
    inherit pkgs;
    prev = packages;
    final = packages;
  };
  portNames = pkgs.lib.concatMap (
    item: if item ? pname then [ item.pname ] else builtins.attrNames item
  ) declarations;
  names =
    if scope == "world" then
      world
    else if scope == "ports" then
      pkgs.lib.unique (world ++ portNames)
    else
      throw "Unknown campaign scope: ${scope}";
  evaluated = map (name: {
    inherit name;
    result = builtins.tryEval packages.${name}.drvPath;
  }) names;
  admitted = builtins.filter (item: item.result.success) evaluated;
  manifest = {
    id = "${scope}-${revision}";
    name = "Fil-C ${scope} · ${toString (builtins.length admitted)} roots";
    inherit source revision scope;
    excluded = map (item: {
      inherit (item) name;
      reason = "derivation evaluation failed";
    }) (builtins.filter (item: !item.result.success) evaluated);
    # Materialise the source even with Determinate's lazy source trees.
    source_path = builtins.path {
      path = flake.outPath;
      name = "filnix-world-source";
    };
    roots = map (item: {
      inherit (item) name;
      drv = item.result.value;
    }) admitted;
  };
in
builtins.toFile "filnix-landmark-world.json" (
  builtins.unsafeDiscardOutputDependency (builtins.toJSON manifest)
)
