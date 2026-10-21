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
  # Flake outputs CI requires in the caches (scripts/ci-outputs.txt), built
  # ahead of the package roots so that publication puts them there first.
  leading =
    map
      (
        attr:
        let
          path = pkgs.lib.splitString "." attr;
        in
        {
          name = pkgs.lib.last path;
          value = pkgs.lib.getAttrFromPath path flake;
        }
      )
      (
        builtins.filter (line: line != "" && !pkgs.lib.hasPrefix "#" line) (
          pkgs.lib.splitString "\n" (
            builtins.readFile "${flake.outPath}/scripts/ci-outputs.txt"
          )
        )
      );
  evaluated =
    map (item: {
      inherit (item) name;
      result = builtins.tryEval item.value.drvPath;
    }) leading
    ++ map (name: {
      inherit name;
      result = builtins.tryEval packages.${name}.drvPath;
    }) (pkgs.lib.subtractLists (map (item: item.name) leading) names);
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
