# finix module: build the whole userland with Fil-C.
#
# `pkgs` becomes a Fil-C package set, so every finix module that says
# `pkgs.foo` gets the Fil-C build of foo without any per-module override.
# Rust and Go packages are marked broken (lib/block-rust-go.nix), so they
# cannot slip into the system unnoticed. Packages named in
# `filc.userland.native` come from the native set of the same Nixpkgs instead;
# the kernel and the bootloader always do.
#
#   imports = [ filnix.finixModules.filc-userland ];
#   filc.userland = {
#     enable = true;
#     system = "aarch64-linux";
#     native = [ "tailscale" ];
#   };
{ filnix }:
{
  config,
  lib,
  ...
}:
let
  cfg = config.filc.userland;
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

    system = mkOption {
      type = types.enum [
        "aarch64-linux"
        "x86_64-linux"
      ];
      example = "aarch64-linux";
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
      defaultText = lib.literalExpression "pkgsFilc.pkgsBuildBuild";
      example = lib.literalExpression "import nixpkgs { system = \"aarch64-linux\"; }";
      description = ''
        The native package set that `filc.userland.native` takes packages
        from. By default, the fully native stage of filnix's own Nixpkgs.
        Your usual Nixpkgs works too and gets its binary cache hits.
        (Not `buildPackages`: its target platform is Fil-C, which matters for
        anything that is itself a compiler, such as Emacs' native compilation.)
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
      # Fil-C cannot build the kernel, and the bootloader runs before any
      # userland does.
      "linuxKernel"
      "linuxPackages"
      "linuxPackages_latest"
      "limine"
      "sbctl" # Go; limine's install hook uses it for secure boot
      "efibootmgr" # and this, to manage EFI boot entries
      # finix creates users and groups with it during activation; Rust.
      "userborn"
      # The setuid wrappers are small static programs. Fil-C does not link
      # statically, and a static build derived from the Fil-C set recurses.
      "pkgsStatic"
      # Only the wrappers use pkgs.glibc, for a header from its source. Fil-C
      # programs get their libc from the Fil-C sysroot, never from here.
      "glibc"
    ]
    ++ lib.optional cfg.nativeNix "nix";

    filc.userland.packages = filnix.lib.${cfg.system}.mkPkgsFilc {
      blockRustGo = true;
      crossOverlays = [
        (
          final: prev:
          let
            native =
              if cfg.nativePackages != null then
                cfg.nativePackages
              else
                final.pkgsBuildBuild;
          in
          lib.genAttrs cfg.native (name: native.${name})
        )
      ];
    };

    nixpkgs.pkgs = cfg.packages;

    services.nix-daemon.settings.sandbox = mkIf (!cfg.nativeNix) false;
  };
}
