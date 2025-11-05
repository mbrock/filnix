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
        mountFilesystems = false; # Docker handles this
      };

  inherit (core) env mkDockerExtraCommands;

in
base.dockerTools.streamLayeredImage {
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
