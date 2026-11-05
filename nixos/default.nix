# NixOS module: a NixOS whose `pkgs` is the Fil-C package set
# (lib/filc-system.nix), so systemd, PAM, D-Bus and every service are
# Fil-C. This adds what only NixOS needs; docs/nixos-userland.md says why.
#
#   imports = [ filnix.nixosModules.default ];
#   filc.enable = true;
{ filnix }:
{ config, lib, ... }:
{
  imports = [
    (import ../lib/filc-system.nix {
      inherit filnix;
      os = "nixos";
    })
  ];

  config = lib.mkIf config.filc.enable {
    # dbus-broker's port is not done; the reference dbus-daemon is.
    services.dbus.implementation = lib.mkDefault "dbus";

    # NixOS loads NSS modules (nss-systemd, myhostname) only into nscd. The
    # Fil-C glibc has no nscd, and nsncd is Rust: a native nsncd could not
    # load the Fil-C modules. Without them, lookups use /etc files only.
    services.nscd.enable = lib.mkDefault false;
    system.nssModules = lib.mkIf (!config.services.nscd.enable) (lib.mkForce [ ]);

    nix.settings.sandbox = lib.mkIf (!config.filc.nativeNix) false;
  };
}
