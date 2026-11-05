# A small finix machine whose whole userland is Fil-C: finit as PID 1,
# mdevd, sysklogd, dhcpcd, OpenSSH, the shell and the tools are Fil-C
# builds; only the kernel and the exceptions in lib/native-exceptions.nix are not.
# Try it:
#
#   nix run .#finixConfigurations.filc-demo.config.system.build.vm
#
# and log in as root (no password) on the console, or
# `ssh -p 2222 demo@localhost` with password "demo". Ctrl-a x quits QEMU.
# finix/test.nix boots it and checks that its processes are Fil-C.
{
  config,
  lib,
  pkgs,
  modules,
  ...
}:
let
  # QEMU runs on the host, so it is the native build.
  native = pkgs.pkgsBuildBuild;
in
{
  imports = with modules; [
    getty
    openssh
    sudo
    dhcpcd
    sysklogd
    nix-daemon
  ];

  filc.enable = true;

  networking.hostName = lib.mkDefault "filc-demo";

  boot.kernelParams = [ "console=ttyS0,115200n8" ];

  # The root file system is a tmpfs; the Nix store is the host's, over 9p.
  fileSystems."/" = {
    device = "tmpfs";
    fsType = "tmpfs";
    options = [ "mode=755" ];
  };

  services.getty.enable = true;
  # The VM runs with -nographic: the login prompt is on the serial console.
  services.getty.ttys = [
    "ttyS0"
    "tty1"
  ];
  services.mdevd.enable = true;
  services.sysklogd.enable = true;
  services.dhcpcd.enable = lib.mkDefault true;
  services.openssh.enable = true;
  services.nix-daemon.enable = true;
  # finix's lix-daemon module, when imported (its test driver imports every
  # module), would make Lix the default; Lix is partly Rust.
  services.nix-daemon.package = pkgs.nix;
  programs.sudo.enable = true;

  users.users.root.password = "";
  users.users.demo = {
    isNormalUser = true;
    password = "$6$filcdemofilcdemo$/GDxfM31Nn0AzYyqqGfxyZb7sJiojyzIFCPaW/9ixsOOmQ.7.mzzZRc/281rrQBqbTdB4DfmWSP9BXML40cH9."; # demo
    extraGroups = [ "wheel" ];
  };

  environment.systemPackages = with pkgs; [
    bashInteractive
    coreutils
    findutils
    gnugrep
    gnused
    gawk
    less
    nano
    curl
    procps
    iproute2
  ];

  virtualisation.memorySize = 2048;
  virtualisation.cores = 2;
  virtualisation.qemu.package = lib.mkDefault native.qemu_kvm;

  system.build.vm = native.writeShellScriptBin "run-filc-demo-vm" ''
    exec ${lib.escapeShellArgs config.virtualisation.qemu.argv} \
      -nographic \
      -nic user,model=virtio-net-pci,hostfwd=tcp::2222-:22 \
      "$@"
  '';
}
