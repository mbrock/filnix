# Overlay consumer for list-based ports2.nix
# Converts list of port specs (with pname) to overlay attrset

pkgs: final: prev:
let
  # Import ports2.nix - returns a list of port specs or attrsets
  # Each item is either:
  #   - A port spec: { pname, attrs, overrideArgs, ... }
  #   - An attrset with explicit names: { foo = <port-spec>; bar = <port-spec>; }
  portList = import ./ports2.nix {
    inherit pkgs;
    inherit prev;
  };

  # Convert list to flat attrset keyed by pname
  # Handles both direct specs and attrset-wrapped specs
  portSpecs = builtins.listToAttrs (
    pkgs.lib.flatten (
      map (
        item:
        if item ? pname then
          # Direct port spec with pname field
          {
            name = item.pname;
            value = item;
          }
        else
          # Attrset with explicit names: { foo = <spec>; bar = <spec>; }
          # Extract each key-value pair
          pkgs.lib.mapAttrsToList (name: spec: {
            inherit name;
            value = spec;
          }) item
      ) portList
    )
  );

  # Apply each spec to the corresponding package in prev
  ported = prev.lib.mapAttrs (
    name: spec:
    if spec ? __customDrv then
      # Custom derivation - call it with final context for auto-injected deps
      (final.callPackage spec.__customDrv { }).overrideAttrs spec.__attrs
    else if prev ? ${name} then
      # Package exists in nixpkgs - apply overlay transformations
      let
        base = if spec.overrideArgs != { } then prev.${name}.override spec.overrideArgs else prev.${name};
      in
      base.overrideAttrs spec.attrs
    else
      # Package not in nixpkgs and not a custom drv - shouldn't happen
      throw "Package '${name}' not found in nixpkgs and no __customDrv provided"
  ) portSpecs;

in
ported
// rec {
  # Emacs package sets using our ported emacs30
  emacsPackages = prev.emacsPackagesFor ported.emacs30;
  emacs30Packages = prev.emacsPackagesFor ported.emacs30;

  # Python aliases - python312 is explicitly named, provides both python3 and python312
  python3 = ported.python312;
  python312Packages = ported.python312.pkgs;
  python3Packages = prev.dontRecurseIntoAttrs python312Packages;

  # pkg-config alias
  pkg-config = prev.pkg-config.override {
    pkg-config = ported.pkgconf-unwrapped;
    baseBinName = "pkgconf";
  };
}
