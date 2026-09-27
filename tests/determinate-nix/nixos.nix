# Several NixOS systems' toplevel drvPaths, forced in parallel by `nix eval --json`.
{ nixpkgs }:
let
  mk =
    extra:
    (import "${nixpkgs}/nixos/lib/eval-config.nix" {
      system = "x86_64-linux";
      modules = [
        {
          boot.loader.grub.enable = false;
          fileSystems."/" = {
            device = "/dev/sda1";
            fsType = "ext4";
          };
          system.stateVersion = "25.11";
          documentation.nixos.enable = false;
        }
        extra
      ];
    }).config.system.build.toplevel.drvPath;
in
{
  minimal = mk { };
  server = mk {
    services.openssh.enable = true;
    services.nginx.enable = true;
    services.postgresql.enable = true;
  };
  desktop = mk {
    services.xserver.enable = true;
    services.xserver.desktopManager.xfce.enable = true;
  };
  containers = mk {
    virtualisation.docker.enable = true;
    networking.firewall.enable = true;
  };
}
