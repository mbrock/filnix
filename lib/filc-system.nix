# The Fil-C system: a NixOS or finix machine whose `pkgs` is filnix's Fil-C
# package set. NixOS and finix modules pick their programs from `pkgs`, so
# systemd or finit, PAM, D-Bus, OpenSSH and every service are Fil-C builds
# without being named here. The kernel, the bootloader and the other
# packages in lib/native-exceptions.nix come from native Nixpkgs, and so do
# the ones you add:
#
#   imports = [ filnix.nixosModules.default ];   # or finixModules.default
#   filc.enable = true;
#   filc.native = native: { inherit (native) tailscale; };
#
# nixos/default.nix and finix/default.nix import this with their `os` and
# add what differs between the two.
{ filnix, os }:
{
  config,
  lib,
  options,
  pkgs,
  ...
}:
let
  cfg = config.filc;
  inherit (lib)
    mkEnableOption
    mkIf
    mkOption
    types
    ;
  exceptions = lib.filterAttrs (
    name: e: lib.elem os e.os && (name != "nix" || cfg.nativeNix)
  ) (import ./native-exceptions.nix);
  nativePkgs =
    if cfg.nativePackages != null then
      cfg.nativePackages
    else
      filnix.lib.${cfg.system}.nativePackages;
  # The user's exceptions, as given to the package set.
  userNative = cfg.native nativePkgs;
  # Every node that sets nothing shares one package set: each one made here
  # is a fresh Nixpkgs import.
  shared =
    options.filc.native.highestPrio >= 1500
    && cfg.nativePackages == null
    && cfg.nativeNix;

  # The store paths of the native exceptions. filc-ps allows a native
  # process whose program is in one's closure. Without string context, so
  # an exception the system does not use is not pulled into it.
  nativeRoots =
    lib.concatMap
      (
        v:
        lib.optionals (lib.isDerivation v) (
          map (o: builtins.unsafeDiscardStringContext v.${o}.outPath) (
            v.outputs or [ "out" ]
          )
        )
      )
      (
        map (n: nativePkgs.${n}) (lib.attrNames exceptions)
        ++ lib.attrValues userNative
      );

  filc-ps = pkgs.writeShellScriptBin "filc-ps" ''
    PATH=${
      lib.makeBinPath [
        pkgs.coreutils
        pkgs.gnugrep
        pkgs.nix
      ]
    }:$PATH
    roots=(${lib.escapeShellArgs nativeRoots})
    ${builtins.readFile ./filc-ps.sh}
  '';
in
{
  # Its definitions are this file's, not those of the module importing it.
  _file = ./filc-system.nix;

  options.filc = {
    enable = mkEnableOption "the Fil-C system: `pkgs` is filnix's Fil-C package set";

    # Not read from nixpkgs.*: this module sets nixpkgs.pkgs, which makes
    # those options unreadable.
    system = mkOption {
      type = types.enum [
        "aarch64-linux"
        "x86_64-linux"
      ];
      default = "x86_64-linux";
      description = "The system to build for.";
    };

    native = mkOption {
      type = types.functionTo (types.attrsOf types.raw);
      default = _: { };
      defaultText = lib.literalExpression "native: { }";
      example = lib.literalExpression "native: { inherit (native) tailscale ripgrep; }";
      description = ''
        Packages to take from the native package set instead of building
        them with Fil-C, as a function of that set. Use it for Rust and Go
        programs you want anyway, and for C programs that do not work yet.
        Each one runs as an ordinary native process with native libraries.
        A name the native set does not have fails evaluation. The packages
        in filnix's lib/native-exceptions.nix are always native.
      '';
    };

    nativePackages = mkOption {
      type = types.nullOr types.raw;
      default = null;
      defaultText = lib.literalExpression "import filnix.inputs.nixpkgs { inherit (config.filc) system; }";
      example = lib.literalExpression "import nixpkgs { system = \"x86_64-linux\"; }";
      description = ''
        The native package set that the exceptions come from. By default,
        filnix's own Nixpkgs, imported natively. Your usual Nixpkgs works
        too and gets its binary cache hits.
      '';
    };

    nativeNix = mkOption {
      type = types.bool;
      default = true;
      description = ''
        Whether Nix itself (the daemon and CLI) is the native build. The
        Fil-C build works but cannot sandbox builds, having no namespaces or
        seccomp; with this off, the build sandbox is turned off too.
      '';
    };

    packages = mkOption {
      type = types.raw;
      readOnly = true;
      description = "The resulting package set, which is also `pkgs`.";
    };
  };

  config = mkIf cfg.enable {
    filc.packages =
      if shared then
        filnix.legacyPackages.${cfg.system}.pkgsFilcSystem.${os}
      else
        filnix.lib.${cfg.system}.mkPkgsFilcSystem {
          inherit os;
          inherit (cfg) native nativeNix;
          nativePackages = nativePkgs;
        };

    nixpkgs.pkgs = cfg.packages;

    assertions =
      map (name: {
        assertion = nativePkgs ? ${name};
        message = "filc: the native package set has no ${name}, a built-in native exception (lib/native-exceptions.nix). Was it renamed in Nixpkgs?";
      }) (lib.attrNames exceptions)
      ++ [
        {
          # An `inherit (native) x` with a typo is lazy; forcing each value
          # stops evaluation at the missing attribute.
          assertion = lib.all (v: builtins.seq v true) (lib.attrValues userNative);
          message = "filc.native: every value must evaluate.";
        }
      ];

    environment.systemPackages = [ filc-ps ];
  };
}
