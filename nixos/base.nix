# The base Fil-C NixOS machine that filnix ships as a disk image: a whole
# Fil-C system (nixos/default.nix) set up to try. The console and the
# serial line log in as `demo`, who has sudo without a password; SSH takes
# keys only. /etc/nixos holds a flake pinned to the filnix revision the
# image was built from, with filc.cachix.org configured, so a first
# `sudo nixos-rebuild switch` substitutes instead of compiling the world.
#
#   nix run github:mbrock/filnix#nixos-vm            # boot it in QEMU
#   nix build github:mbrock/filnix#nixos-image       # the compressed qcow2
#
# `system.build.qcow2` builds the image with the native package set: the
# disk image tools (rsync, parted, e2fsprogs, lkl, qemu-img) come from
# `pkgs` in Nixpkgs' make-disk-image, and here `pkgs` is Fil-C.
{ filnix }:
{
  config,
  lib,
  modulesPath,
  pkgs,
  ...
}:
let
  rev = filnix.rev or "main";
  cache = {
    substituter = "https://filc.cachix.org";
    key = "filc.cachix.org-1:8rA7kXyu1HaJuMTsAKfA9fU/+r8YtLv5KiZ5hfDNZMk=";
  };
  native =
    if config.filc.nativePackages != null then
      config.filc.nativePackages
    else
      filnix.lib.${config.filc.system}.nativePackages;

  # What /etc/nixos starts with. `nixos-rebuild` picks the configuration
  # named after the host.
  flake = pkgs.writeText "flake.nix" ''
    {
      # The filnix revision this machine was built from. Change it to update.
      inputs.filnix.url = "github:mbrock/filnix/${rev}";

      nixConfig.extra-substituters = [ "${cache.substituter}" ];
      nixConfig.extra-trusted-public-keys = [ "${cache.key}" ];

      outputs = { filnix, ... }: {
        nixosConfigurations.${config.networking.hostName} = filnix.lib.nixosSystem {
          modules = [
            filnix.nixosModules.base
            ./configuration.nix
          ];
        };
      };
    }
  '';
  configuration = pkgs.writeText "configuration.nix" ''
    # Your changes to the base Fil-C machine (filnix's nixos/base.nix).
    # Apply them with: sudo nixos-rebuild switch
    { pkgs, ... }:
    {
      # Programs and services come from `pkgs`, which is Fil-C:
      # environment.systemPackages = [ pkgs.git pkgs.htop ];
      # services.lighttpd.enable = true;

      # Rust and Go programs have no Fil-C build; keep them native:
      # filc.native = native: { inherit (native) ripgrep; };

      # Log in over SSH with your key:
      # users.users.demo.openssh.authorizedKeys.keys = [ "ssh-ed25519 AAAA..." ];
    }
  '';
in
{
  imports = [ "${modulesPath}/profiles/qemu-guest.nix" ];

  filc.enable = true;

  boot.loader.grub.device = lib.mkDefault "/dev/vda";
  boot.loader.timeout = 1;
  boot.growPartition = true;
  fileSystems."/" = {
    device = "/dev/disk/by-label/nixos";
    fsType = "ext4";
    autoResize = true;
  };
  # The serial console last, so it gets the kernel's and systemd's output.
  boot.kernelParams = [
    "console=tty0"
    "console=ttyS0,115200n8"
  ];

  networking.hostName = lib.mkDefault "filc";

  users.users.demo = {
    isNormalUser = true;
    extraGroups = [ "wheel" ];
  };
  services.getty.autologinUser = "demo";
  security.sudo.wheelNeedsPassword = false;

  services.openssh = {
    enable = true;
    settings = {
      PasswordAuthentication = false;
      KbdInteractiveAuthentication = false;
      PermitRootLogin = "no";
    };
  };

  users.motd = ''

    This is NixOS with a Fil-C userland: systemd, PAM, OpenSSH, Bash and
    every service are memory-safe Fil-C builds. `sudo filc-ps` shows that
    nothing else runs native but the allowed exceptions.

    You are logged in as demo, with sudo and no password. SSH takes keys
    only. /etc/nixos is a flake pinned to filnix ${builtins.substring 0 12 rev}; edit
    configuration.nix there and run `sudo nixos-rebuild switch`. Give the
    machine at least 2 GiB of memory.

  '';

  nix.settings = {
    experimental-features = [
      "nix-command"
      "flakes"
    ];
    extra-substituters = [ cache.substituter ];
    extra-trusted-public-keys = [ cache.key ];
  };

  # Copied once, so that they can be edited.
  systemd.tmpfiles.rules = [
    "d /etc/nixos 0755 root root -"
    "C /etc/nixos/flake.nix - - - - ${flake}"
    "C /etc/nixos/configuration.nix - - - - ${configuration}"
    "z /etc/nixos/flake.nix 0644 root root -"
    "z /etc/nixos/configuration.nix 0644 root root -"
  ];

  # Not git: `github:` flake inputs come as tarballs, and the Fil-C git
  # with its Perl, Python and GnuPG would double the image.
  environment.systemPackages = with pkgs; [
    nano
    curl
  ];

  system.stateVersion = "26.05";

  system.build.qcow2 = import "${native.path}/nixos/lib/make-disk-image.nix" {
    pkgs = native;
    inherit lib config;
    name = "filnix-nixos-image";
    baseName = "filnix-nixos-${config.system.nixos.label}";
    format = "qcow2-compressed";
    partitionTableType = "legacy";
    # Room for a few rebuilds; free space compresses away. growpart takes
    # the root file system further on a bigger disk.
    additionalSpace = "8G";
    copyChannel = false;
    memSize = 2048;
  };
}
