# The options of filnix's modules as evaluation knows them, as JSON for
# dterm-nix's option index (dterm_nix.pl --options). For each option: where
# it is declared, its type, default, example and description, and the
# files that define it in an evaluated system. The options are the ones a
# module declares and the ones it sets, so the index follows the modules
# without being edited by hand.
#
# Paths are relative: "nixos/filc.nix" in filnix, "nixpkgs/…" in Nixpkgs.
{
  lib,
  # Nixpkgs' eval-config.nix, applied to a system and modules.
  evalNixos,
  # The NixOS module and the file it is in, and the machine whose
  # definitions are listed (nixos/demo.nix).
  nixosModule,
  nixosModuleFile,
  nixosMachine,
  # The finix module and its file, evaluated here with
  # filc.userland.enable set.
  finixModule,
  finixModuleFile,
  filnixRoot,
  nixpkgsRoot,
  nixpkgsRev,
}:
let
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

  # The module is a function of filnix, so its file is stated: without it
  # its definitions would be attributed to the flake.
  nixos = evalNixos [
    {
      _file = nixosModuleFile;
      imports = [ nixosModule ];
    }
    nixosMachine
  ];

  nixosSet =
    let
      m = nixosModule (
        nixos._module.args
        // {
          inherit (nixos) config options;
          inherit lib;
        }
      );
      paths = lib.unique (setPaths nixos.options [ ] m.config);
    in
    lib.filter (p: lib.head p != "filc") paths;

  finix = lib.evalModules {
    modules = [
      {
        _file = finixModuleFile;
        imports = [ finixModule ];
      }
      {
        _file = "dterm-nix/options.nix";
        _module.check = false;
        filc.userland = {
          enable = true;
          system = "x86_64-linux";
        };
      }
    ];
  };
in
{
  inherit nixpkgsRev;
  nixos = {
    machine = rel nixosMachine;
    options =
      map (entry "declared") (options nixos.options.filc)
      ++ map (p: entry "set" (lib.getAttrFromPath p nixos.options)) nixosSet;
  };
  finix = {
    machine = "dterm-nix/options.nix";
    options = map (entry "declared") (options finix.options.filc.userland);
  };
}
