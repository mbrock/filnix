# Native package metadata only: no derivation paths, source realization, or builds.
# The caller must disable import-from-derivation as an additional boundary.
{
  nixpkgsPath,
  names ? null,
}:
let
  pkgs = import nixpkgsPath {
    system = "x86_64-linux";
    overlays = [ ];
    config = {
      allowAliases = false;
      # These permit metadata inspection, not permission to build these packages.
      allowBroken = true;
      allowUnfree = true;
      allowUnsupportedSystem = true;
      allowInsecurePredicate = _: true;
    };
  };
  inherit (pkgs) lib;
  attempt = value: builtins.tryEval (builtins.deepSeq value value);
  inputNames = inputs: map (p: p.pname or p.name or "<unnamed-input>") inputs;
  inspect =
    name:
    let
      p = pkgs.${name};
      fields = {
        pname = p.pname or name;
        version = p.version or null;
        description = p.meta.description or "";
        position = p.meta.position or null;
        availableOnLinux = lib.meta.availableOn pkgs.stdenv.hostPlatform p;
        broken = p.meta.broken or false;
        sourceProvenance = map (s: s.shortName or "unknown") (
          p.meta.sourceProvenance or [ ]
        );
        isLinuxKernel =
          let
            flags = p.buildFlags or [ ];
          in
          builtins.isList flags
          && builtins.elem "vmlinux" flags
          && lib.any (lib.hasPrefix "KBUILD_BUILD_VERSION=") flags;
        hasSource = p ? src && p.src != null;
        hasCompiler = p.stdenv.hasCC or false;
        dontBuild = p.dontBuild or false;
        dontConfigure = p.dontConfigure or false;
        doCheck = p.doCheck or false;
        doInstallCheck = p.doInstallCheck or false;
        nativeBuildInputs = inputNames (p.nativeBuildInputs or [ ]);
        buildInputs = inputNames (p.buildInputs or [ ]);
        propagatedBuildInputs = inputNames (p.propagatedBuildInputs or [ ]);
        nativeCheckInputs = inputNames (p.nativeCheckInputs or [ ]);
        checkInputs = inputNames (p.checkInputs or [ ]);
        # The active builder's attributes are stronger evidence than matching a
        # compiler somewhere in its transitive build-time dependency closure.
        builderHints = {
          rust = p ? cargoDeps || p ? cargoHash || p ? cargoLock;
          go = p ? goModules || p ? vendorHash;
          haskell = p ? isHaskellLibrary;
          python = (p.pythonModule or null) != null;
          ocaml = p ? duneVersion;
          node = p ? npmDeps || p ? yarnOfflineCache;
        };
      };
      values = builtins.mapAttrs (_: attempt) fields;
      result = attempt (
        if !lib.isDerivation p then
          {
            attrPath = [ name ];
            status = "not-a-package";
          }
        else
          {
            attrPath = [ name ];
            status = "evaluated";
            metadata = builtins.mapAttrs (
              _: v: if v.success then v.value else null
            ) values;
            unavailableFields = builtins.attrNames (
              lib.filterAttrs (_: v: !v.success) values
            );
          }
      );
    in
    if result.success then
      result.value
    else
      {
        attrPath = [ name ];
        status = "evaluation-error";
      };
in
if names == null then builtins.attrNames pkgs else map inspect names
