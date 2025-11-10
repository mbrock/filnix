# Convert pythonPorts.nix list to packageOverrides function

pkgs:
let
  # Import pyports.nix - returns a list of port specs
  portList = import ../pyports.nix { inherit pkgs; };

  # Convert list to attrset keyed by pname (same logic as ports2-as-overlay)
  portSpecs = builtins.listToAttrs (
    pkgs.lib.flatten (
      map (item:
        if builtins.isString item then
          # String means pname is embedded, extract it
          { name = item; value = { }; }
        else if item ? pname then
          # Direct port spec with pname field
          { name = item.pname; value = item; }
        else
          # Attrset with explicit names
          pkgs.lib.mapAttrsToList (name: spec: {
            inherit name;
            value = spec;
          }) item
      ) portList
    )
  );
in
# Return a packageOverrides function
pyself: pyprev:
  pkgs.lib.mapAttrs (
    name: spec:
      if spec == { } then
        pyprev.${name} or null
      else if spec ? __customPython then
        # Custom Python package (not in pyprev)
        spec.__customPython pyself
      else if spec ? attrs && builtins.isFunction spec.attrs then
        # Normal port - apply overrides
        let
          base = if spec.overrideArgs != { } then pyprev.${name}.override spec.overrideArgs else pyprev.${name};
        in
        base.overrideAttrs spec.attrs
      else
        pyprev.${name}
  ) portSpecs

