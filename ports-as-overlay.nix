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
  # Import ports.nix in overlay mode
  # Each port is either:
  #   - An attrs function: old -> { patches = ...; ... }
  #   - A custom derivation spec: { __customDrv = path; __deps = {}; __attrs = fn }
  portSpecs = import ./ports.nix {
    inherit pkgs;
    mode = "overlay";
  };

in
# Apply each spec to the corresponding package in prev
pkgs.lib.mapAttrs (
  name: spec:
  if spec ? __customDrv then
    # Custom derivation (e.g., OpenSSL) - call it with final context for deps
    # callPackage will auto-inject dependencies, then we override with __deps, then apply attrs
    ((final.callPackage spec.__customDrv { }).override spec.__deps).overrideAttrs spec.__attrs
  else
    # Normal patch/attrs overlay
    prev.${name}.overrideAttrs spec
) portSpecs
