# Evaluate only: creates an immutable manifest with references to the source
# and derivations, not their realised outputs. No package builds are requested.
{
  source,
  revision,
  scope ? "expected",
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
    if scope == "expected" then
      import "${flake.outPath}/ports/expected.nix"
    else if scope == "world" then
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
  failed = builtins.filter (item: !item.result.success) evaluated;
  # The first four consumers failed through PipeWire in ports-a324a843;
  # sfml_2/SDL_compat/smpeg also fail evaluation through it once marked broken.
  # Retain the known blocker even outside the expected selection, but only
  # while PipeWire is broken and the consumer still fails evaluation.
  pipewireConsumers = [
    "wireplumber"
    "sdl3"
    "sdl2-compat"
    "cava"
    "sfml_2"
    "SDL_compat"
    "smpeg"
  ];
  knownNames = [ "pipewire" ] ++ pipewireConsumers;
  knownExcluded = builtins.filter (
    name:
    packages.pipewire.meta.broken
    && !(builtins.tryEval packages.${name}.drvPath).success
  ) knownNames;
  reasonFor =
    name:
    if builtins.elem name knownExcluded then
      (if name == "pipewire" then "" else "Depends on broken pipewire: ")
      + packages.pipewire.meta.filcBrokenReason
    else
      let
        reason = builtins.tryEval (
          packages.${name}.meta.filcBrokenReason
            or "derivation evaluation failed (unresolved)"
        );
      in
      if reason.success then
        reason.value
      else
        "derivation evaluation failed (unresolved)";
  admitted = builtins.filter (item: item.result.success) evaluated;
  manifest = {
    id = "${scope}-${revision}";
    name = "Fil-C ${scope} · ${toString (builtins.length admitted)} roots";
    inherit source revision scope;
    selection =
      if scope == "expected" then
        "ports/expected.nix"
      else if scope == "ports" then
        "world + declared ports (exploratory)"
      else
        "shells/world-packages.nix";
    excluded = map (name: {
      inherit name;
      reason = reasonFor name;
      selected = builtins.elem name (map (item: item.name) evaluated);
    }) (pkgs.lib.unique ((map (item: item.name) failed) ++ knownExcluded));
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
assert
  scope == "expected"
  ->
    pkgs.lib.assertMsg (failed == [ ])
      "Expected campaign evaluation failed: ${
        pkgs.lib.concatMapStringsSep ", " (item: item.name) failed
      }";
builtins.toFile "filnix-landmark-world.json" (
  builtins.unsafeDiscardOutputDependency (builtins.toJSON manifest)
)
