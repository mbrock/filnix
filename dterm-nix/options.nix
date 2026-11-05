# The options of filnix's modules as evaluation knows them, as JSON for
# dterm-nix's option index (dterm_nix.pl --options). For each option: where
# it is declared, its type, default, example and description, and the
# files that define it in an evaluated system. The options are the ones a
# module declares and the ones it sets, so the index follows the modules
# without being edited by hand.
#
# Paths are relative: "lib/filc-system.nix" in filnix, "nixpkgs/…" in Nixpkgs.
{
  lib,
  # Nixpkgs' eval-config.nix, applied to a system and modules.
  evalNixos,
  # The flake, whose exported modules are listed, and the build
  # platform's package set that ports/overlay.nix is applied with.
  filnix,
  pkgs,
  nixpkgsRoot,
  nixpkgsRev,
}:
let
  filnixRoot = filnix.outPath;

  # The exported modules: each with the file it is in and the machine it
  # is evaluated in. The machine only supplies definitions; the options
  # listed are the ones declared in the module's file and the ones its
  # config sets. Both exported modules import the shared core,
  # lib/filc-system.nix, which is listed on its own: `module` is the
  # function in `file` whose config is walked, when it is not the exported
  # module itself. A module the flake does not export (yet) is left out.
  here = "dterm-nix/options.nix";
  nixosMachine = {
    _file = here;
    filc.enable = true;
    boot.loader.grub.enable = false;
    fileSystems."/".device = "none";
    system.stateVersion = "26.05";
  };
  finixMachine = {
    _file = here;
    filc.enable = true;
  };
  modules = lib.filter (m: lib.hasAttrByPath m.attr filnix) [
    {
      attr = [
        "nixosModules"
        "default"
      ];
      name = "filc-system";
      title = "NixOS and finix: lib/filc-system.nix";
      kind = "nixos";
      file = "${filnixRoot}/lib/filc-system.nix";
      module = import "${filnixRoot}/lib/filc-system.nix" {
        inherit filnix;
        os = "nixos";
      };
      machine = nixosMachine;
      machineFile = here;
    }
    {
      attr = [
        "nixosModules"
        "default"
      ];
      kind = "nixos";
      file = "${filnixRoot}/nixos/default.nix";
      machine = nixosMachine;
      machineFile = here;
    }
    {
      attr = [
        "finixModules"
        "default"
      ];
      kind = "finix";
      file = "${filnixRoot}/finix/default.nix";
      machine = finixMachine;
      machineFile = here;
    }
  ];

  rel =
    file:
    let
      f = builtins.unsafeDiscardStringContext (toString file);
      root = toString filnixRoot + "/";
      np = toString nixpkgsRoot + "/";
    in
    if lib.hasPrefix root f then
      lib.removePrefix root f
    else if lib.hasPrefix np f then
      "nixpkgs/" + lib.removePrefix np f
    else
      f;

  text =
    v:
    if v == null then
      null
    else if builtins.isString v then
      builtins.unsafeDiscardStringContext v
    else if v ? _type && v ? text then
      {
        kind = v._type;
        text = builtins.unsafeDiscardStringContext v.text;
      }
    else
      builtins.unsafeDiscardStringContext (lib.generators.toPretty { } v);

  # What the option's documentation says, as the manual renders it.
  doc =
    opt:
    let
      entries = lib.optionAttrSetToDocList { x = opt; };
      e = lib.findFirst (e: e.loc == opt.loc) { } entries;
      tried = builtins.tryEval (builtins.deepSeq (text (e.default or null)) e);
    in
    if tried.success then tried.value else { };

  entry =
    group: opt:
    let
      d = doc opt;
      # Only the default (mkOptionDefault, priority 1500) is not a definition.
      defs = builtins.tryEval (
        if (opt.highestPrio or 100) >= 1500 then
          [ ]
        else
          lib.unique (map (x: rel x.file) opt.definitionsWithLocations)
      );
    in
    {
      inherit group;
      name = lib.showOption opt.loc;
      loc = map builtins.unsafeDiscardStringContext opt.loc;
      declarations = map (p: {
        file = rel p.file;
        inherit (p) line;
      }) (opt.declarationPositions or [ ]);
      type = text (d.type or null);
      default = text (d.default or null);
      example = text (d.example or null);
      description = text (d.description or null);
      readOnly = d.readOnly or false;
      definitions = if defs.success then defs.value else [ ];
    };

  options = tree: lib.collect lib.isOption tree;

  # The options a module's config sets: its definitions walked through
  # mkMerge, mkIf and the overrides, down to the first path that is an
  # option.
  setPaths =
    allOptions: prefix: v:
    let
      here = lib.attrByPath prefix null allOptions;
      t = v._type or null;
    in
    if prefix != [ ] && lib.isOption here then
      [ prefix ]
    else if t == "merge" then
      lib.concatMap (setPaths allOptions prefix) v.contents
    else if t == "if" || t == "override" || t == "order" then
      setPaths allOptions prefix v.content
    else if lib.isAttrs v && !lib.isDerivation v && t == null then
      lib.concatLists (
        lib.mapAttrsToList (n: setPaths allOptions (prefix ++ [ n ])) v
      )
    else
      [ ];

  # Which attributes of the Fil-C package set that ports/overlay.nix makes
  # (a port or one of its overrides) are a derivation: those of the same
  # name and derivation, among the names that begin with its first word
  # (bash for bash-interactive, php for php-with-extensions).
  pkgsFilc = filnix.legacyPackages.${pkgs.stdenv.hostPlatform.system}.pkgsFilc;
  overlayNames = builtins.attrNames (
    import "${filnixRoot}/ports/overlay.nix" pkgs pkgsFilc pkgsFilc
  );
  builtBy =
    v:
    let
      word = lib.head (
        lib.splitString "-" (v.pname or (builtins.parseDrvName v.name).name)
      );
      same =
        n:
        let
          r = builtins.tryEval (
            let
              c = pkgsFilc.${n};
            in
            lib.isDerivation c && c.name == v.name && c.drvPath == v.drvPath
          );
        in
        r.success && r.value;
    in
    lib.filter same (lib.filter (lib.hasPrefix word) overlayNames);

  # The value of a set option in the evaluated machine, when it is a
  # package or a list of them: the derivation's name and pname, and the
  # overlay's attributes that build it.
  pkgValue =
    v:
    if lib.isDerivation v then
      let
        attrs = builtBy v;
        pname = v.pname or null;
        # Neither a port nor an override builds it: it is the package set's
        # attribute of that pname, as Nixpkgs builds it, with Fil-C.
        plain =
          let
            r = builtins.tryEval (
              pname != null
              && !(lib.elem pname overlayNames)
              && pkgsFilc ? ${pname}
              && pkgsFilc.${pname}.drvPath == v.drvPath
            );
          in
          attrs == [ ] && r.success && r.value;
      in
      {
        inherit (v) name;
        inherit pname attrs plain;
      }
    else
      null;
  value =
    v:
    let
      r = builtins.tryEval (
        let
          x =
            if lib.isDerivation v then
              [ (pkgValue v) ]
            else if builtins.isList v && v != [ ] && lib.all lib.isDerivation v then
              map pkgValue v
            else
              null;
        in
        builtins.deepSeq x x
      );
    in
    if r.success then r.value else null;

  # A module is a function of filnix, so its file is stated: without it
  # its definitions would be attributed to the flake.
  evaluate =
    m:
    let
      exported = lib.getAttrFromPath m.attr filnix;
      module = m.module or exported;
      inMachine = [
        {
          _file = m.file;
          imports = [ exported ];
        }
        m.machine
      ];
      eval =
        if m.kind == "nixos" then
          evalNixos inMachine
        else
          lib.evalModules {
            modules = inMachine ++ [ { _module.check = false; } ];
          };
      declared = lib.filter (
        o: lib.any (p: rel p.file == rel m.file) (o.declarationPositions or [ ])
      ) (options eval.options);
      applied = module (
        eval._module.args
        // {
          inherit (eval) config options;
          inherit lib;
        }
      );
      setPaths' = lib.filter (p: !(lib.any (o: o.loc == p) declared)) (
        lib.unique (setPaths eval.options [ ] (applied.config or { }))
      );
      # The value in the machine; of a list, the module's own elements.
      setEntry =
        p:
        let
          opt = lib.getAttrFromPath p eval.options;
          v = lib.attrByPath p null eval.config;
          own = builtins.tryEval (
            lib.concatMap (d: lib.toList d.value) (
              lib.filter (d: rel d.file == rel m.file) opt.definitionsWithLocations
            )
          );
        in
        entry "set" opt
        // {
          value = value (
            if builtins.isList v then (if own.success then own.value else null) else v
          );
        };
    in
    {
      inherit (m) kind;
      name = m.name or (lib.concatStringsSep "." m.attr);
      title = m.title or null;
      file = rel m.file;
      machine = rel m.machineFile;
      options = map (entry "declared") declared ++ map setEntry setPaths';
    };
in
{
  inherit nixpkgsRev overlayNames;
  modules = map evaluate modules;
}
