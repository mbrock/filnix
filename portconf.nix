# DSL for defining Fil-C ports
#
# This module provides a compositional DSL for defining package ports.
# Instead of passing large attribute sets, we use a pipeline of small
# transformations that are easier to read and maintain.

{
  lib,
  fix,
  base,
}:

let
  inherit (lib) foldl';

  # The builder we transform (endofunctor target)
  Init = {
    deps = { };
    attrs = (_: { }); # old -> { ... }
    tranquilize = false;
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
  overAttrs = f: fa: fa // { attrs = merge fa.attrs f; };
  overTranquilize = f: fa: fa // { tranquilize = f; };

  # Primitives
  arg = kv: overDeps kv;

  # `use` embeds any (old: { ... }) transform or plain attrset
  use =
    f:
    overAttrs (if builtins.isAttrs f && !builtins.isFunction f then (_: f) else f);

  tranquilize = overTranquilize true;

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
        src = base.fetchurl {
          url = urlf v;
          hash = h;
        };
        version = v;
        pname = pname;
        name = "${pname}-${v}";
      }
    );

  # Build a single port from a list [basePkg step1 step2 ...]
  # Plain attrsets are automatically wrapped with arg
  buildPort =
    steps:
    let
      pkg = builtins.head steps;
      rawSteps = builtins.tail steps;
      normalizeStep =
        step:
        if builtins.isAttrs step && !builtins.isFunction step then arg step else step;
      normalizedSteps = builtins.map normalizeStep rawSteps;
      acc = foldl' (fa: step: step fa) Init normalizedSteps;
    in
    fix pkg {
      deps = acc.deps;
      attrs = acc.attrs;
      tranquilize = acc.tranquilize;
    };

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
      patches = builtins.filter (patch: !(lib.hasInfix p (toString patch))) (
        old.patches or [ ]
      );
    });
  removeCFlag =
    flag:
    use (old: {
      env = (old.env or { }) // {
        NIX_CFLAGS_COMPILE = lib.replaceStrings [ flag ] [ "" ] (
          (old.env or { }).NIX_CFLAGS_COMPILE or ""
        );
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
  configure =
    flag:
    use (old: {
      configureFlags = (old.configureFlags or [ ]) ++ [ flag ];
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
  inherit arg use src;
  inherit
    skipTests
    skipCheck
    parallelize
    tranquilize
    tool
    link
    patch
    skipPatch
    removeCFlag
    addCFlag
    configure
    wip
    ;
  inherit github gnu gnuTarGz;
}
