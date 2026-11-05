# NixOS module: a NixOS whose `pkgs` is the Fil-C package set
# (lib/filc-system.nix), so systemd, PAM, D-Bus and every service are
# Fil-C. This adds what only NixOS needs; docs/nixos-userland.md says why.
#
#   imports = [ filnix.nixosModules.default ];
#   filc.enable = true;
{ filnix }:
{
  config,
  lib,
  pkgs,
  ...
}:
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

    # PrivateUsers= makes systemd unshare(CLONE_NEWUSER), which the kernel
    # refuses a multithreaded process, and the Fil-C runtime always runs
    # threads of its own: every unit with it (mosquitto, redis, tor, ...)
    # failed at step USER. Turn it off; their other sandboxing stays. Since
    # "no" is the default, a drop-in for all services changes just the units
    # that set it, upstream unit files included. The name sorts after units'
    # own drop-ins. docs/filc-findings.md has the runtime side.
    systemd.packages = [
      (pkgs.writeTextDir "etc/systemd/system/service.d/zz-filc-no-private-users.conf" ''
        [Service]
        PrivateUsers=no
      '')
      # IOSchedulingClass= and IOSchedulingPriority= call ioprio_set, a
      # system call the Fil-C runtime has no wrapper for; Fil-C systemd gets
      # ENOSYS and the unit fails at step IOPRIO (logrotate did). Empty
      # values unset them, so services run at the default IO priority.
      (pkgs.writeTextDir "etc/systemd/system/service.d/zz-filc-no-ioprio.conf" ''
        [Service]
        IOSchedulingClass=
        IOSchedulingPriority=
      '')
      # Mount units run systemd's mount(8), from util-linux-minimal, whose
      # libmount probes the new mount API with fsopen(NULL) when it uses a
      # helper (mount.davfs, mount.nfs, FUSE), and the Fil-C runtime stops
      # it there. Patching util-linux-minimal would rebuild nearly every
      # package, so these use the classic mount(2) instead; the full
      # util-linux, whose mount(8) is on PATH, carries the fix
      # (docs/filc-findings.md).
      (pkgs.writeTextDir "etc/systemd/system/mount.d/zz-filc-classic-mount.conf" ''
        [Mount]
        Environment=LIBMOUNT_FORCE_MOUNT2=always
      '')
    ];
  };
}
