# The packages a Fil-C system always takes from native Nixpkgs, with the
# operating systems that need each one and why. A process is either all
# Fil-C or all native, so each exception is a whole package.
#
# lib/filc-system.nix asserts that every name exists in the native package
# set, so a rename in Nixpkgs fails evaluation. The table in docs/nixos.md
# is generated from this file (tests/native-exceptions-table.nix).
let
  both = [
    "nixos"
    "finix"
  ];
  nixos = [ "nixos" ];
  finix = [ "finix" ];
in
{
  linuxKernel = {
    os = both;
    why = "Fil-C cannot build the kernel.";
  };
  linuxPackages = {
    os = both;
    why = "The kernel and its modules.";
  };
  linuxPackages_latest = {
    os = both;
    why = "The kernel and its modules.";
  };
  pkgsStatic = {
    os = both;
    why = "The setuid wrappers are small static programs. Fil-C does not link statically, and a static set derived from the Fil-C one recurses.";
  };
  glibc = {
    os = both;
    why = "Only the setuid wrappers use it, for a header from its source. Fil-C programs get their libc from the Fil-C sysroot.";
  };
  nix = {
    os = both;
    why = "Unless `filc.nativeNix = false`. The Fil-C Nix works but cannot sandbox builds: Fil-C has no namespaces or seccomp.";
  };

  grub2 = {
    os = nixos;
    why = "The bootloader runs before any userland, and its package holds the boot images as well as the tools that install them.";
  };
  kexec-tools = {
    os = nixos;
    why = "kexec loads a kernel together with its purgatory, freestanding code that runs between the two kernels.";
  };
  fish = {
    os = nixos;
    why = "Rust (fish 4). users-groups.nix compares every user's shell with `pkgs.fish`, so it must evaluate; a user who picks fish gets the native one.";
  };
  nixos-init = {
    os = nixos;
    why = "Rust: the initrd's initrd-find-nixos-closure and, with `system.nixos-init`, stage 2's init and activation.";
  };
  makeInitrdNGTool = {
    os = nixos;
    why = "Rust: builds the initrd, and generate-shutdown-ramfs runs it on the machine.";
  };
  switch-to-configuration-ng = {
    os = nixos;
    why = "Rust: switch-to-configuration, which talks to systemd over D-Bus.";
  };

  limine = {
    os = finix;
    why = "The bootloader runs before any userland.";
  };
  sbctl = {
    os = finix;
    why = "Go; limine's install hook uses it for secure boot.";
  };
  efibootmgr = {
    os = finix;
    why = "limine's install hook uses it to manage EFI boot entries.";
  };
  userborn = {
    os = finix;
    why = "Rust; finix creates users and groups with it during activation.";
  };
}
