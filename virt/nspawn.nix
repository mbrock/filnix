{
  pkgs,
  ports,
  world-pkgs,
}:

let
  common = import ./common.nix { inherit pkgs ports; };
  inherit (common) ghostty-terminfo dank-bashrc lighttpd-demo;

  core =
    import ./core.nix
      {
        inherit
          pkgs
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
pkgs.runCommand "filc-runit-nspawn-standalone" { } (mkRootfsScript "$out")
