# Wrapper to use ports.nix as a cross-compilation overlay
# This is the judo: same ports.nix definitions, interpreted as overlay!
#
# In overlay mode:
# - Dependencies are ignored (cross-compilation rebuilds them automatically)
# - Only patches and attribute transformations are applied
# - The result is a pure overlay that works with nixpkgs cross-compilation

pkgs:

final: prev:
let
  # Import ports.nix - returns attribute transformers for each package
  # Each port is either:
  #   - An attrs function: old -> { patches = ...; ... }
  #   - A custom derivation spec: { __customDrv = path; __deps = {}; __attrs = fn }
  portSpecs = import ./ports.nix { inherit pkgs; };

in
# Apply each spec to the corresponding package in prev
pkgs.lib.mapAttrs (
  name: spec:
  if spec ? __customDrv then
    # Custom derivation (e.g., OpenSSL) - call it with final context for deps
    # callPackage will auto-inject dependencies from final (cross-compiled pkgs)
    # then we override with __deps, then apply __attrs
    let
      base = final.callPackage spec.__customDrv { };
      withDeps = if spec.__deps != {} then base.override spec.__deps else base;
    in
    withDeps.overrideAttrs spec.__attrs
  else if prev ? ${name} then
    # Package exists in nixpkgs - apply overlay transformations
    # First apply function argument overrides, then attribute overrides
    let
      base = if spec.overrideArgs != {} then prev.${name}.override spec.overrideArgs else prev.${name};
    in
    base.overrideAttrs spec.attrs
  else
    # New package not in nixpkgs - create it from scratch
    # This handles packages like kittydoom that use pkgs.callPackage
    let
      # Try to get the base package from the port definition
      # This is a hack - ideally we'd store this info in the port spec
      basePkg =
        if name == "kittydoom" then
          final.callPackage ./kitty-doom.nix { }
        else if name == "wasm3" then
          final.callPackage ./wasm3.nix { }
        else
          throw "Cannot create new package '${name}' - base package info not available";
      withArgs = if spec.overrideArgs != {} then basePkg.override spec.overrideArgs else basePkg;
    in
    withArgs.overrideAttrs spec.attrs
) portSpecs
