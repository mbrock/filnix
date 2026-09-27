# NixOS module: run chosen services and programs as Fil-C builds.
#
# Only the selected packages change. The rest of the system, including
# systemd, glibc and the kernel, stays the ordinary NixOS build, so the
# Fil-C programs sit alongside native ones.
#
#   imports = [ filnix.nixosModules.filc ];
#   filc.enable = true;                      # every switch below
#   filc.nix.enable = false;                 # ...except this one
#   filc.tools = [ "coreutils" "curl" ];     # programs on PATH
{ filnix }:
{
  config,
  lib,
  pkgs,
  ...
}:
let
  cfg = config.filc;
  fp = cfg.packages;
  inherit (lib)
    mkEnableOption
    mkIf
    mkMerge
    mkOption
    types
    ;

  # A switch that follows filc.enable unless set explicitly.
  switch =
    what:
    mkOption {
      type = types.bool;
      default = cfg.enable;
      defaultText = lib.literalExpression "config.filc.enable";
      description = "Whether to use the Fil-C build of ${what}.";
    };
in
{
  options.filc = {
    enable = mkEnableOption "the Fil-C builds of every service and program below";

    packages = mkOption {
      type = types.raw;
      default = filnix.legacyPackages.${pkgs.stdenv.hostPlatform.system}.pkgsFilc;
      defaultText = lib.literalExpression "filnix.legacyPackages.\${system}.pkgsFilc";
      description = "The Fil-C package set that replacements come from.";
    };

    openssh.enable = switch "the OpenSSH daemon (services.openssh)";
    shell.enable = switch "Bash as the login shell of root and normal users";
    tor.enable = switch "Tor (services.tor)";
    unbound.enable = switch "the Unbound resolver (services.unbound)";
    lighttpd.enable = switch "lighttpd (services.lighttpd)";

    nix.enable = switch ''
      Nix itself (the daemon and the CLI). Fil-C has no namespaces or
      seccomp, so this also turns off the build sandbox'';

    tools = mkOption {
      type = types.listOf types.str;
      default = [ ];
      example = [
        "coreutils"
        "curl"
        "git"
      ];
      description = ''
        Attributes of filc.packages to put on the system PATH, ahead of the
        native programs of the same name.
      '';
    };
  };

  config = mkMerge [
    (mkIf cfg.openssh.enable {
      services.openssh.package = fp.openssh;
      # A Fil-C program can't dlopen the system's native PAM modules, so
      # sshd checks passwords and keys itself (no logind session).
      services.openssh.settings.UsePAM = lib.mkDefault false;
    })

    (mkIf cfg.shell.enable {
      users.defaultUserShell = fp.bashInteractive;
      users.users.root.shell = fp.bashInteractive;
      environment.shells = [ fp.bashInteractive ];
    })

    (mkIf cfg.tor.enable {
      services.tor.package = fp.tor;
    })

    (mkIf cfg.unbound.enable {
      # The service is Type=notify, so it needs the systemd-enabled build.
      services.unbound.package = fp.unbound-with-systemd;
    })

    (mkIf cfg.lighttpd.enable {
      services.lighttpd.package = fp.lighttpd;
    })

    (mkIf cfg.nix.enable {
      nix.package = fp.nix;
      nix.settings.sandbox = false;
    })

    {
      environment.systemPackages = map (name: lib.hiPrio fp.${name}) cfg.tools;
    }
  ];
}
