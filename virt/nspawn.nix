{
  base,
  ports,
  world-pkgs,
}:

let
  common = import ./common.nix { inherit base ports; };
  inherit (common) ghostty-terminfo dank-bashrc lighttpd-demo;

  core =
    import ./core.nix
      {
        inherit
          base
          ports
          world-pkgs
          dank-bashrc
          ghostty-terminfo
          lighttpd-demo
          ;
      }
      {
        consoleDevice = "/dev/console";
        mountFilesystems = false; # systemd-nspawn handles this
      };

  inherit (core) env mkRootfsScript;

in
base.runCommand "filc-runit-nspawn-standalone" { } (mkRootfsScript "$out")
