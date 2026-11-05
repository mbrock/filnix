# The base Fil-C NixOS (nixos/base.nix) as an Amazon EC2 machine, for the
# public AMI that .github/workflows/ami.yml registers. Root logs in over SSH
# with the instance's EC2 key; the serial console logs `demo` in.
#
# `system.build.ami` is the VHD to import, built with the native package
# set like the qcow2, with Nixpkgs' image-info.json beside it.
{ filnix }:
{
  config,
  lib,
  modulesPath,
  ...
}:
let
  native =
    if config.filc.nativePackages != null then
      config.filc.nativePackages
    else
      filnix.lib.${config.filc.system}.nativePackages;
in
{
  imports = [
    (import ./base.nix { inherit filnix; })
    "${modulesPath}/virtualisation/amazon-image.nix"
  ];

  # EC2 names the host otherwise; /etc/nixos/flake.nix names the
  # configuration after it.
  networking.hostName = "filc";
  # ec2-data puts the instance's key in root's authorized_keys.
  services.openssh.settings.PermitRootLogin = lib.mkForce "prohibit-password";
  # The SSM agent is Go.
  services.amazon-ssm-agent.enable = lib.mkForce false;
  # It turns user data into /etc/nixos/configuration.nix for channels, and
  # brings in git; this machine's configuration is the flake in /etc/nixos.
  virtualisation.amazon-init.enable = false;

  system.build.ami = import "${native.path}/nixos/lib/make-disk-image.nix" {
    pkgs = native;
    inherit lib config;
    name = "filnix-nixos-ami";
    baseName = "filnix-nixos-${config.system.nixos.label}";
    format = "vpc";
    partitionTableType = "legacy+gpt";
    # An 8 GiB volume by default, with room for a rebuild; a bigger volume
    # at launch is grown into.
    diskSize = 8192;
    copyChannel = false;
    memSize = 2048;
    postVM = ''
      ${native.jq}/bin/jq -n \
        --arg label ${lib.escapeShellArg config.system.nixos.label} \
        --arg file "$diskImage" \
        --arg logical_bytes "$(${native.qemu-utils}/bin/qemu-img info --output json "$diskImage" | ${native.jq}/bin/jq '."virtual-size"')" \
        '{ label: $label, boot_mode: "legacy-bios", system: "x86_64-linux",
           file: $file, logical_bytes: $logical_bytes }' \
        > $out/nix-support/image-info.json
    '';
  };
}
