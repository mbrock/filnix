# DSL for defining Fil-C ports as pure overlays
#
# This module provides a compositional DSL for defining package ports that work
# seamlessly with Nix cross-compilation infrastructure. Each port is a pipeline
# of small transformations applied to a base package.
#
# Key design principles:
# - Pure overlays: No manual dependency tracking
# - Composable: Each transformation is a small, focused function
# - Cross-compilation native: Dependencies auto-resolved by nixpkgs
#
# Each port returns: { attrs = old -> { ... }; overrideArgs = { ... } }
# OR for custom derivations: { __customDrv = path; __attrs = fn }
#
# Example:
#   zlib = port [
#     pkgs.zlib                    # Base package from nixpkgs
#     (src "1.3" urlFn hash)       # Override version and source
#     (patch ./my.patch)           # Add a patch
#     (arg { enableStatic = true; }) # Pass arg to .override
#     skipTests                    # Disable tests
#   ];

{
  lib,
  pkgs,
}:

let
  inherit (lib) foldl';

  # The builder we transform (endofunctor target)
  Init = {
    overrideArgs = { }; # Function arguments for .override
    attrs = (_: { }); # old -> { ... }
  };

  # Compose two attrs fns - thread changes through and merge results
  merge =
    f: g:
    (
      old:
      let
        step1 = f old;
        step2 = g (old // step1);
      in
      step1 // step2
    );

  # Endofunctor "port step" = FixArgs -> FixArgs
  overArgs = a: fa: fa // { overrideArgs = fa.overrideArgs // a; };
  overAttrs = f: fa: fa // { attrs = merge fa.attrs f; };

  # Primitives
  arg = kv: overArgs kv;

  # `use` embeds any (old: { ... }) transform or plain attrset
  use = f: overAttrs (if builtins.isAttrs f && !builtins.isFunction f then (_: f) else f);

  # Mark a package as broken for Fil-C (prevents accidental dependencies)
  # Only marks as broken when cross-compiling to filc targets
  broken = reason: {
    attrs = old: {
      meta = (old.meta or {}) // (
        if (old.stdenv.hostPlatform.isFilc or false) ||
           (lib.hasInfix "filc" (old.stdenv.hostPlatform.config or ""))
        then {
          broken = true;
          description = (old.meta.description or "Package") + " (not available for Fil-C: ${reason})";
        }
        else {}
      );
    };
    overrideArgs = {};
  };

  serialize = overAttrs (old: {
    # set parallel building to false
    enableParallelBuilding = false;
  });

  # Cohesive source step: version + URL mapping + hash
  # usage: (src "3.10" (v: "https:// ftp/${v}.tar.xz") "sha256-...")
  src =
    v: urlf: h:
    use (
      old:
      let
        pname = old.pname or (builtins.parseDrvName old.name).name;
      in
      {
        src = pkgs.fetchurl {
          url = urlf v;
          hash = h;
        };
        version = v;
        pname = pname;
        name = "${pname}-${v}";
      }
    );

  # Build a single port from a list [basePkg step1 step2 ...]
  # Use arg({ ... }) to pass function arguments to .override
  # Use use({ ... }) or other DSL functions to modify package attributes
  # Returns { attrs = old -> { ... }; overrideArgs = { ... } }
  # OR for custom derivations: { __customDrv = path; __attrs = fn }
  buildPort =
    steps:
    let
      pkg = builtins.head steps;
      rawSteps = builtins.tail steps;

      # Check if this is a custom derivation (path to .nix file)
      isCustomDrv = builtins.isPath pkg || (builtins.isString pkg && lib.hasSuffix ".nix" pkg);

      # All steps must be functions that transform our Init structure
      # Plain attrsets are no longer supported - use arg() or use() explicitly
      acc = foldl' (fa: step: step fa) Init rawSteps;
    in
    if isCustomDrv then
      # Custom derivation - return special structure for overlay to callPackage
      { __customDrv = pkg; __attrs = acc.attrs; }
    else
      # Normal port - return attrs and overrideArgs for overlay use
      { inherit (acc) attrs overrideArgs; };

  # Common helpers
  skipTests = use (_: {
    doCheck = false;
    doInstallCheck = false;
  });
  skipCheck = use (_: {
    doCheck = false;
  });
  parallelize = use (_: {
    enableParallelBuilding = true;
  });
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
  wip = throw "This port is marked as work-in-progress and cannot be built yet";

  # Wrapper for nm that strips pizlonated_ prefix from symbols
  # Some build systems need to see "clean" symbol names
  depizloing-nm = pkgs.writeShellScriptBin "nm" ''
    ${pkgs.binutils}/bin/nm "$@" | sed 's/\bpizlonated_//g'
  '';

  # URL builders
  # GitHub releases: owner/repo and path function
  # Usage: github "owner/repo" (v: "v${v}/pkg-${v}.tar.gz")
  github =
    orgRepo: path: v:
    let
      parts = lib.splitString "/" orgRepo;
      org = builtins.elemAt parts 0;
      repo = builtins.elemAt parts 1;
    in
    "https://github.com/${org}/${repo}/releases/download/${path v}";

  # GNU mirror: package name
  # Usage: gnu "sed" (v: "https://ftpmirror.gnu.org/sed/sed-${v}.tar.xz")
  gnu = pkg: v: "mirror://gnu/${pkg}/${pkg}-${v}.tar.xz";
  gnuTarGz = pkg: v: "mirror://gnu/${pkg}/${pkg}-${v}.tar.gz";

in
{
  inherit buildPort;
  inherit arg use src broken;
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
    configure
    removeConfigureFlag
    wip
    depizloing-nm
    ;
  inherit github gnu gnuTarGz;
}
