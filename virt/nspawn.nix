{
  base,
  ports,
  world-pkgs,
  dank-bashrc,
  ghostty-terminfo,
}:

let
  core =
    import ./core.nix
      {
        inherit
          base
          ports
          world-pkgs
          dank-bashrc
          ghostty-terminfo
          ;
      }
      {
        consoleDevice = "/dev/console";
        mountFilesystems = false; # systemd-nspawn handles this
      };

  inherit (core) env mkRootfsScript;

in
base.runCommand "filc-runit-nspawn-standalone" { } (mkRootfsScript "$out")
