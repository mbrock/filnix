{
  config,
  modulesPath,
  pkgs,
  lib,
  ...
}:
{
  imports = [ (modulesPath + "/profiles/qemu-guest.nix") ];

  networking.hostName = "filc-vm";

  # Root with no password for testing
  users.users.root.initialPassword = "";

  boot.kernelParams = [ "console=ttyS0" ];
  boot.consoleLogLevel = lib.mkDefault 7;
  boot.growPartition = true;

  boot.loader.grub = {
    efiSupport = true;
    efiInstallAsRemovable = true;
    device = "nodev";
  };

  fileSystems."/" = {
    device = "/dev/vda2";
    fsType = "ext4";
  };
  fileSystems."/boot" = {
    device = "/dev/vda1";
    fsType = "vfat";
  };

  system.stateVersion = "24.05";
}
