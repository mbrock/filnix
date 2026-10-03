# Evaluate only: creates an immutable manifest with references to the source
# and derivations, not their realised outputs. No package builds are requested.
{ source, revision }:
let
  flake = builtins.getFlake source;
  packages = flake.legacyPackages.x86_64-linux.pkgsFilc;
  names = import "${flake.outPath}/shells/world-packages.nix";
  manifest = {
    id = "landmark-world-${revision}";
    name = "Fil-C landmark world · ${toString (builtins.length names)} roots";
    inherit source revision;
    # Materialise the source even with Determinate's lazy source trees.
    source_path = builtins.path {
      path = flake.outPath;
      name = "filnix-world-source";
    };
    roots = map (name: {
      inherit name;
      drv = packages.${name}.drvPath;
    }) names;
  };
in
builtins.toFile "filnix-landmark-world.json" (
  builtins.unsafeDiscardOutputDependency (builtins.toJSON manifest)
)
