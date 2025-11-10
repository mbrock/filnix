# DSL for list-based Fil-C ports (portconf2)
#
# Simplified and optimized for the list-based structure.
# Key improvements:
# - pin: Simple version override that reuses existing URL patterns
# - Cleaner composition
# - Designed for overlay-native workflows

{
  lib,
  pkgs,
}:

let
  inherit (lib) foldl';

  # The state we transform through the pipeline
  Init = {
    overrideArgs = { }; # Args for .override
    attrs = (_: { }); # Attrs for .overrideAttrs
  };

  # Compose two attribute transformers
  merge =
    f: g: old:
    let
      step1 = f old;
      step2 = g (old // step1);
    in
    step1 // step2;

  # State transformers
  overArgs = a: st: st // { overrideArgs = st.overrideArgs // a; };
  overAttrs = f: st: st // { attrs = merge st.attrs f; };

  # Core primitives
  arg = kv: overArgs kv;
  use = f: overAttrs (if builtins.isAttrs f && !builtins.isFunction f then (_: f) else f);

  # Pin a specific version and hash
  # Automatically substitutes version in the existing URL
  # Usage: pin "2.1.12" "sha256-..."
  pin =
    version: hash:
    use (
      old:
      let
        pname = old.pname or (builtins.parseDrvName old.name).name;
        oldVersion = old.version or "";

        # Get the original URL and replace old version with new version
        # This handles most common URL patterns automatically
        originalUrl =
          if old.src ? urls then
            builtins.head old.src.urls
          else if old.src ? url then
            old.src.url
          else
            throw "Cannot extract URL from ${pname} source";

        # Replace old version with new version in URL
        # Try multiple patterns: x.y.z, x.y, x_y_z, etc.
        newUrl = lib.replaceStrings [ oldVersion ] [ version ] originalUrl;
      in
      {
        inherit version pname;
        name = "${pname}-${version}";
        src = pkgs.fetchurl {
          url = newUrl;
          inherit hash;
        };
      }
    );

  # Full source override (for when pin doesn't work)
  # Usage: src "2.1.12" "sha256-..." (v: "https://.../${v}.tar.gz")
  src =
    version: hash: urlFn:
    use (
      old:
      let
        pname = old.pname or (builtins.parseDrvName old.name).name;
      in
      {
        inherit version pname;
        name = "${pname}-${version}";
        src = pkgs.fetchurl {
          url = urlFn version;
          inherit hash;
        };
      }
    );

  # Extract pname from package
  extractPname =
    pkg:
    if pkg ? pname then
      pkg.pname
    else if pkg ? name then
      (builtins.parseDrvName pkg.name).name
    else
      throw "Cannot extract pname from package";

  # Build a port with automatic pname extraction
  # Usage: for pkgs.coreutils [skipCheck]
  #        for "flask" [skipCheck]  (for Python/sub-overlays)
  # For explicit names: { bash = for pkgs.bash [...]; }
  for =
    pkg: steps:
    let
      isCustomDrv = builtins.isPath pkg || (builtins.isString pkg && lib.hasSuffix ".nix" pkg);
      isStringName = builtins.isString pkg && !lib.hasSuffix ".nix" pkg;
      pname =
        if isStringName then
          pkg
        else if isCustomDrv then
          null
        else
          extractPname pkg;
      acc = foldl' (st: step: step st) Init steps;
      spec =
        if isCustomDrv then
          {
            __customDrv = pkg;
            __attrs = acc.attrs;
          }
        else
          { inherit (acc) attrs overrideArgs; };
    in
    spec // { inherit pname; };

  # Common helpers
  # reason parameter is for documentation only - doesn't affect the build
  skipTests =
    reason:
    use {
      doCheck = false;
      doInstallCheck = false;
    };

  skipCheck =
    reason:
    use {
      doCheck = false;
    };
  parallelize = use { enableParallelBuilding = true; };
  serialize = use { enableParallelBuilding = false; };

  tool =
    x:
    use (old: {
      nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ x ];
    });
  link =
    x:
    use (old: {
      buildInputs = (old.buildInputs or [ ]) ++ [ x ];
    });

  patch =
    p:
    use (old: {
      patches = (old.patches or [ ]) ++ [ p ];
    });
  skipPatch =
    p:
    use (old: {
      patches = builtins.filter (patch: !(lib.hasInfix p (toString patch))) (old.patches or [ ]);
    });

  removeCFlag =
    flag:
    use (old: {
      env = (old.env or { }) // {
        NIX_CFLAGS_COMPILE = lib.replaceStrings [ flag ] [ "" ] ((old.env or { }).NIX_CFLAGS_COMPILE or "");
      };
      preConfigure = (old.preConfigure or "") + ''
        export NIX_CFLAGS_COMPILE="''${NIX_CFLAGS_COMPILE//${flag}/}"
      '';
    });

  addCFlag =
    flag:
    use (old: {
      env = (old.env or { }) // {
        NIX_CFLAGS_COMPILE = ((old.env or { }).NIX_CFLAGS_COMPILE or "") + " ${flag}";
      };
    });

  addCMakeFlag =
    flag:
    use (old: {
      cmakeFlags = (old.cmakeFlags or [ ]) ++ [ flag ];
    });
  removeCMakeFlag =
    flag:
    use (old: {
      cmakeFlags = builtins.filter (f: f != flag) (old.cmakeFlags or [ ]);
    });

  configure =
    flag:
    use (old: {
      configureFlags = (old.configureFlags or [ ]) ++ [ flag ];
    });
  removeConfigureFlag =
    flag:
    use (old: {
      configureFlags = builtins.filter (f: f != flag) (old.configureFlags or [ ]);
    });

  addMakeFlag =
    flag:
    use (old: {
      makeFlags = (old.makeFlags or [ ]) ++ [ flag ];
    });
  removeMakeFlag =
    flag:
    use (old: {
      makeFlags = builtins.filter (f: f != flag) (old.makeFlags or [ ]);
    });

  addMesonFlag =
    flag:
    use (old: {
      mesonFlags = (old.mesonFlags or [ ]) ++ [ flag ];
    });
  removeMesonFlag =
    flag:
    use (old: {
      mesonFlags = builtins.filter (f: f != flag) (old.mesonFlags or [ ]);
    });

  # Mark as broken for Fil-C with a reason
  # Only sets broken/badPlatforms when actually cross-compiling to Fil-C
  broken =
    reason:
    use (
      old:
      let
        isFilcTarget =
          (old.stdenv.hostPlatform.isFilc or false)
          || (lib.hasInfix "filc" (old.stdenv.hostPlatform.config or ""));
      in
      if isFilcTarget then
        {
          meta = (old.meta or { }) // {
            broken = true;
            badPlatforms = (old.meta.badPlatforms or [ ]) ++ [ old.stdenv.hostPlatform.system ];
            description = (old.meta.description or "Package") + " (Fil-C: ${reason})";
          };
        }
      else
        {
          meta = old.meta or { };
        }
    );

  # Mark packages as memory-safe when built with Fil-C
  # Removes knownVulnerabilities since memory safety eliminates whole classes of bugs
  markAsNotNecessarilyInsecure = use (old: {
    meta = (old.meta or { }) // {
      knownVulnerabilities = [ ];
      description = (old.meta.description or "Package") + " (Memory-safe via Fil-C)";
    };
  });

  wip = throw "Work in progress";

  # Utilities
  depizloing-nm = pkgs.writeShellScriptBin "nm" ''
    ${pkgs.binutils}/bin/nm "$@" | sed 's/\bpizlonated_//g'
  '';

  # URL helpers
  github =
    orgRepo: pathFn: v:
    let
      parts = lib.splitString "/" orgRepo;
      org = builtins.elemAt parts 0;
      repo = builtins.elemAt parts 1;
    in
    "https://github.com/${org}/${repo}/releases/download/${pathFn v}";

  gnu = pkg: v: "mirror://gnu/${pkg}/${pkg}-${v}.tar.xz";
  gnuTarGz = pkg: v: "mirror://gnu/${pkg}/${pkg}-${v}.tar.gz";

in
{
  inherit for;
  inherit
    arg
    use
    pin
    src
    broken
    markAsNotNecessarilyInsecure
    ;
  inherit
    skipTests
    skipCheck
    parallelize
    serialize
    tool
    link
    patch
    skipPatch
    removeCFlag
    addCFlag
    removeCMakeFlag
    addCMakeFlag
    addMakeFlag
    removeMakeFlag
    addMesonFlag
    removeMesonFlag
    configure
    removeConfigureFlag
    wip
    depizloing-nm
    ;
  inherit github gnu gnuTarGz;
}
