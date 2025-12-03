pkgs:
let
  inherit (pkgs) lib;

  baseGemConfig = pkgs.defaultGemConfig;

  portList = import ../rubyports.nix { inherit pkgs; };

  portSpecs = builtins.listToAttrs (
    lib.flatten (
      map (
        item:
        if builtins.isString item then
          {
            name = item;
            value = { };
          }
        else if item ? pname then
          {
            name = item.pname;
            value = item;
          }
        else
          lib.mapAttrsToList (name: spec: {
            inherit name;
            value = spec;
          }) item
      ) portList
    )
  );

  specToFn =
    spec:
    if spec == { } then
      (_attrs: { })
    else if spec ? attrs && builtins.isFunction spec.attrs then
      spec.attrs
    else
      (_attrs: { });

  composedGemConfig = lib.mapAttrs (
    name: spec:
    let
      ourFn = specToFn spec;
    in
    if baseGemConfig ? ${name} then
      attrs:
      let
        nixpkgsResult = baseGemConfig.${name} attrs;
        attrsWithNixpkgs = attrs // nixpkgsResult;
        ourResult = ourFn attrsWithNixpkgs;
      in
      nixpkgsResult // ourResult
    else
      ourFn
  ) portSpecs;

in
composedGemConfig
