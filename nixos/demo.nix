# A small NixOS machine whose daemons and tools are Fil-C builds. Try it:
#
#   nix run .#nixosConfigurations.filc-demo.config.system.build.vm
#
# and log in as root (no password) on the console, or `ssh -p 2222 demo@localhost`
# with password "demo".
{
  modulesPath,
  pkgs,
  ...
}:
{
  imports = [ "${modulesPath}/virtualisation/qemu-vm.nix" ];

  filc.enable = true;
  filc.tools = [
    "coreutils"
    "findutils"
    "gnugrep"
    "gnused"
    "gawk"
    "diffutils"
    "gnutar"
    "xz"
    "zstd"
    "file"
    "less"
    "nano"
    "tmux"
    "curl"
    "git"
    "jq"
    "sqlite"
    "python3"
    "perl"
  ];

  # /share/doc would pull every tool's doc output; Python's fails to build.
  documentation.doc.enable = false;

  networking.hostName = "filc-demo";

  services.openssh = {
    enable = true;
    settings.PasswordAuthentication = true;
  };

  services.unbound.enable = true;

  services.lighttpd = {
    enable = true;
    document-root = pkgs.writeTextDir "index.html" ''
      <h1>Served by Fil-C lighttpd</h1>
    '';
  };
  networking.firewall.allowedTCPPorts = [
    22
    80
  ];

  users.users.root.initialHashedPassword = "";
  users.users.demo = {
    isNormalUser = true;
    password = "demo";
    extraGroups = [ "wheel" ];
  };

  services.getty.helpLine = ''
    The OpenSSH daemon, Bash, Unbound, lighttpd, Nix and the tools on PATH
    are Fil-C builds; `filc-status` lists them.
  '';

  virtualisation = {
    memorySize = 4096;
    cores = 4;
    forwardPorts = [
      {
        from = "host";
        host.port = 2222;
        guest.port = 22;
      }
      {
        from = "host";
        host.port = 8080;
        guest.port = 80;
      }
    ];
  };

  system.stateVersion = "26.05";
}
