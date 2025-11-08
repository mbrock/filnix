# DSL for defining Fil-C ports as overlays
#
# This module provides a compositional DSL for defining package ports.
# Instead of passing large attribute sets, we use a pipeline of small
# transformations that are easier to read and maintain.
#
# Each port returns an attribute transformer: old -> { patches = ...; ... }
# Dependencies are handled automatically by Nix cross-compilation.

{
  lib,
  pkgs,
}:

let
  inherit (lib) foldl';

  # The builder we transform (endofunctor target)
  Init = {
    deps = { };
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
  overDeps = d: fa: fa // { deps = fa.deps // d; };
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
  # Plain attrsets without wrapping are treated as deps (ignored in overlay mode)
  # Use arg({ ... }) to mark as function arguments for .override
  # Returns { attrs = old -> { ... }; overrideArgs = { ... } }
  # OR for custom derivations: { __customDrv = path; __deps = {}; __attrs = fn }
  buildPort =
    steps:
    let
      pkg = builtins.head steps;
      rawSteps = builtins.tail steps;

      # Check if this is a custom derivation (path to .nix file)
      isCustomDrv = builtins.isPath pkg || (builtins.isString pkg && lib.hasSuffix ".nix" pkg);

      # Plain attrsets become deps (will be ignored), use arg() for override args
      normalizeStep = step: if builtins.isAttrs step && !builtins.isFunction step then overDeps step else step;
      normalizedSteps = builtins.map normalizeStep rawSteps;
      acc = foldl' (fa: step: step fa) Init normalizedSteps;
    in
    if isCustomDrv then
      # Custom derivation - return special structure for overlay to callPackage
      { __customDrv = pkg; __deps = acc.deps; __attrs = acc.attrs; }
    else
      # Normal port - return attrs and overrideArgs for overlay use
      # Dependencies (deps field) are ignored - cross-compilation rebuilds them automatically
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
    ;
  inherit github gnu gnuTarGz;
}
