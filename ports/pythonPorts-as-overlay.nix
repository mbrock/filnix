# Convert pythonPorts.nix list to packageOverrides function

pkgs:
let
  # Import pyports.nix - returns a list of port specs
  portList = import ../pyports.nix { inherit pkgs; };

  # Convert list to attrset keyed by pname (same logic as ports2-as-overlay)
  portSpecs = builtins.listToAttrs (
    pkgs.lib.flatten (
      map (
        item:
        if builtins.isString item then
          # String means pname is embedded, extract it
          {
            name = item;
            value = { };
          }
        else if item ? pname then
          # Direct port spec with pname field
          {
            name = item.pname;
            value = item;
          }
        else
          # Attrset with explicit names
          pkgs.lib.mapAttrsToList (name: spec: {
            inherit name;
            value = spec;
          }) item
      ) portList
    )
  );

  # Test suites run under the Fil-C interpreter (pytestCheckHook is not
  # spliced), but nativeCheckInputs resolve to the build platform's Python
  # set, whose extension modules Fil-C Python cannot load (fonttools failed
  # importing a glibc build of zopfli). Take Python modules among the check
  # inputs from the host set; other check tools and all build tools stay
  # native. An overrideAttrs that adds check inputs later bypasses this.
  hostCheckModules =
    stdenv:
    stdenv
    // {
      mkDerivation =
        fnOrAttrs:
        stdenv.mkDerivation (
          finalAttrs:
          let
            attrs = if builtins.isFunction fnOrAttrs then fnOrAttrs finalAttrs else fnOrAttrs;
            toHost =
              x: if x ? pythonModule && !builtins.isBool x.pythonModule then x.__spliced.hostTarget or x else x;
          in
          attrs
          // pkgs.lib.optionalAttrs (attrs ? nativeInstallCheckInputs) {
            nativeInstallCheckInputs = map toHost attrs.nativeInstallCheckInputs;
          }
        );
    };
in
# Return a packageOverrides function. The Fil-C python passes packageOverrides
# on to its pythonOnBuildForHost, so leave that (native) set alone.
pyself: pyprev:
let
  inherit (pyprev.python.stdenv) hostPlatform buildPlatform;
in
pkgs.lib.optionalAttrs (hostPlatform.config != buildPlatform.config) (
  {
    buildPythonPackage = pyprev.buildPythonPackage.override {
      stdenv = hostCheckModules pyprev.python.stdenv;
    };
    buildPythonApplication = pyprev.buildPythonApplication.override {
      stdenv = hostCheckModules pyprev.python.stdenv;
    };
  }
  // pkgs.lib.mapAttrs (
    name: spec:
    if spec == { } then
      pyprev.${name} or null
    else if spec ? __customPython then
      # Custom Python package (not in pyprev)
      spec.__customPython pyself
    else if spec ? attrs && builtins.isFunction spec.attrs then
      # Normal port - apply overrides
      let
        base =
          if spec.overrideArgs != { } then pyprev.${name}.override spec.overrideArgs else pyprev.${name};
      in
      base.overrideAttrs spec.attrs
    else
      pyprev.${name}
  ) portSpecs
)
