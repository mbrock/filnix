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
        mountFilesystems = false; # Docker handles this
      };

  inherit (core) env mkDockerExtraCommands;

in
pkgs.dockerTools.streamLayeredImage {
  name = "filc-runit";
  tag = "latest";
  architecture = "amd64";

  contents = [ env ];

  config = {
    Entrypoint = [ "/bin/runit-init" ];
    Env = [
      "PATH=${env}/bin"
      "TERMINFO_DIRS=/usr/share/terminfo"
    ];
    WorkingDir = "/root";
  };

  extraCommands = mkDockerExtraCommands;
}
