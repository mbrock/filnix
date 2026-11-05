# NixOS module: build the whole userland with Fil-C.
#
# `pkgs` becomes a Fil-C package set, so systemd, D-Bus, util-linux, PAM,
# coreutils and every service a NixOS module starts are Fil-C builds without
# per-service overrides. The kernel, the bootloader and the initrd's systemd
# stay native, together with the short list below; docs/nixos-userland.md
# says why each one is there.
#
#   imports = [ filnix.nixosModules.filc-userland ];
#   filc.userland.enable = true;
#   filc.userland.native = [ "tailscale" ];
{ filnix }:
{
  config,
  lib,
  ...
}:
let
  cfg = config.filc.userland;
  # A Nixpkgs of its own, not pkgsFilc.pkgsBuildBuild: the variants that
  # one derives, such as pkgsStatic, inherit the Fil-C crossSystem's
  # replaceCrossStdenv and get filcc.
  nativePkgs =
    if cfg.nativePackages != null then
      cfg.nativePackages
    else
      import filnix.inputs.nixpkgs { system = cfg.system; };
  inherit (lib)
    mkEnableOption
    mkIf
    mkOption
    types
    ;
in
{
  options.filc.userland = {
    enable = mkEnableOption "a Fil-C userland: `pkgs` is filnix's Fil-C package set";

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
      type = types.listOf types.str;
      default = [ ];
      example = [ "tailscale" ];
      description = ''
        Top-level package attributes to take from the native package set
        instead of building them with Fil-C. Use this for Rust and Go
        programs you want anyway, and for C programs that do not work yet.
        Each one runs as an ordinary native process, with native libraries.
      '';
    };

    nativePackages = mkOption {
      type = types.nullOr types.raw;
      default = null;
      defaultText = lib.literalExpression "import filnix.inputs.nixpkgs { inherit (config.filc.userland) system; }";
      description = ''
        The native package set that `filc.userland.native` takes packages
        from. By default, filnix's own Nixpkgs, imported natively.
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
    filc.userland.native = [
      # Fil-C cannot build the kernel.
      "linuxKernel"
      "linuxPackages"
      "linuxPackages_latest"
      # The bootloader runs before any userland, and GRUB's package holds the
      # boot images as well as the tools that install them.
      "grub2"
      # kexec loads a kernel together with its purgatory, freestanding code
      # that runs between the two kernels.
      "kexec-tools"
      # The setuid wrappers are small static programs. Fil-C does not link
      # statically, and a static build derived from the Fil-C set recurses.
      "pkgsStatic"
      # Only the wrappers use pkgs.glibc, for a header from its source. Fil-C
      # programs get their libc from the Fil-C sysroot, never from here.
      "glibc"
      # fish 4 is Rust. users-groups.nix compares every user's shell with
      # pkgs.fish, which must therefore evaluate; a user who picks fish gets
      # the native one.
      "fish"
      # Rust: the initrd's initrd-find-nixos-closure and, with
      # system.nixos-init, stage 2's init and activation.
      "nixos-init"
      # Rust: builds the initrd, and generate-shutdown-ramfs runs it on the
      # machine.
      "makeInitrdNGTool"
      # Rust: switch-to-configuration, which talks to systemd over D-Bus.
      "switch-to-configuration-ng"
    ]
    ++ lib.optional cfg.nativeNix "nix";

    filc.userland.packages = filnix.lib.${cfg.system}.mkPkgsFilc {
      blockRustGo = true;
      crossOverlays = [
        (final: prev: lib.genAttrs cfg.native (name: nativePkgs.${name}))
      ];
    };

    nixpkgs.pkgs = cfg.packages;

    # dbus-broker's port is not done (docs/nixos-userland.md); the
    # reference dbus-daemon is.
    services.dbus.implementation = lib.mkDefault "dbus";

    # NixOS loads NSS modules (nss-systemd, myhostname) only into nscd. The
    # Fil-C glibc has no nscd, and nsncd is Rust: a native nsncd could not
    # load the Fil-C modules. Without them, lookups use /etc files only.
    # docs/nixos-userland.md, "NSS".
    services.nscd.enable = lib.mkDefault false;
    system.nssModules = lib.mkIf (!config.services.nscd.enable) (lib.mkForce [ ]);

    nix.settings.sandbox = mkIf (!cfg.nativeNix) false;
  };
}
