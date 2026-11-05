# finix module: a finix system whose `pkgs` is the Fil-C package set
# (lib/filc-system.nix), so finit, PAM, OpenSSH and every service are
# Fil-C. This adds what only finix needs.
#
#   imports = [ filnix.finixModules.default ];
#   filc.enable = true;
{ filnix }:
{ config, lib, ... }:
{
  imports = [
    (import ../lib/filc-system.nix {
      inherit filnix;
      os = "finix";
    })
  ];

  config = lib.mkIf config.filc.enable {
    services.nix-daemon.settings.sandbox = lib.mkIf (
      !config.filc.nativeNix
    ) false;
  };
}
