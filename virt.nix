{ pkgs, ports, filcc, world-pkgs }:
{
  filc-nspawn = import ./virt/nspawn.nix {
    inherit pkgs ports filcc;
    inherit world-pkgs;
  };

  filc-qemu = import ./virt/qemu.nix {
    inherit pkgs ports filcc;
    inherit world-pkgs;
  };

  filc-docker = import ./virt/docker.nix {
    inherit pkgs ports filcc;
    inherit world-pkgs;
  };
}
