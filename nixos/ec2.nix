# An EC2 machine using the Fil-C module (formerly github:mbrock/ec2filc).
#
#   nixos-rebuild switch --flake .#ec2-filc --target-host root@HOST
#   nix build .#nixosConfigurations.ec2-filc.config.system.build.amazonImage
#
# Replace the SSH key with your own before deploying. The Fil-C binary cache
# (https://filc.cachix.org) saves most of the build; it has no auditing or
# security guarantees.
{ modulesPath, ... }:
let
  key = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIJD7B4saBw7XXHcNMeO8MVudPSUDWwzje5y0lLQPP7Ub mikael@brockman.se";
in
{
  imports = [ "${modulesPath}/virtualisation/amazon-image.nix" ];

  filc.enable = true;
  filc.tools = [
    "coreutils"
    "findutils"
    "gnugrep"
    "gnused"
    "gawk"
    "xz"
    "file"
    "less"
    "nano"
    "tmux"
    "curl"
    "git"
    "nethack"
    "figlet"
    "emacs30"
  ];

  nix.settings = {
    experimental-features = [
      "nix-command"
      "flakes"
    ];
    extra-substituters = [ "https://filc.cachix.org" ];
    extra-trusted-public-keys = [
      "filc.cachix.org-1:8rA7kXyu1HaJuMTsAKfA9fU/+r8YtLv5KiZ5hfDNZMk="
    ];
  };

  networking.hostName = "ec2-filc";
  # /share/doc would pull every tool's doc output; Python's fails to build.
  documentation.doc.enable = false;

  services.openssh.enable = true;
  services.tor = {
    enable = true;
    client.enable = true;
  };

  security.sudo.wheelNeedsPassword = false;
  users.users.root.openssh.authorizedKeys.keys = [ key ];
  users.users.mbrock = {
    isNormalUser = true;
    extraGroups = [ "wheel" ];
    openssh.authorizedKeys.keys = [ key ];
  };

  system.stateVersion = "26.05";
}
