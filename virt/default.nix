{
  base,
  ports,
  world-pkgs,
  dank-bashrc,
  ghostty-terminfo,
}:

let
  commonArgs = {
    inherit
      base
      ports
      world-pkgs
      dank-bashrc
      ghostty-terminfo
      ;
  };
in
{
  # systemd-nspawn container (directory rootfs)
  nspawn = base.callPackage ./nspawn.nix commonArgs;

  # QEMU VM (image rootfs)
  qemu = base.callPackage ./qemu.nix commonArgs;

  # Docker image (streamLayeredImage)
  docker = base.callPackage ./docker.nix commonArgs;
}
