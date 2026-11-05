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

  filnix.configuration = lib.mkDefault "amazon";
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

  # Instead, user data of the form `#filnix FLAKE#CONFIGURATION` switches
  # the machine to that configuration once, at first boot, substituting
  # everything (scripts/launch-demo-wiki uses it). Other user data is ignored.
  systemd.services.filnix-first-switch = {
    description = "Switch to the configuration named in the user data";
    wantedBy = [ "multi-user.target" ];
    wants = [ "network-online.target" ];
    after = [
      "network-online.target"
      "fetch-ec2-metadata.service"
    ];
    unitConfig.ConditionPathExists = "!/var/lib/filnix-first-switch/done";
    path = [
      config.nix.package
      config.system.build.nixos-rebuild
    ];
    serviceConfig = {
      Type = "oneshot";
      StateDirectory = "filnix-first-switch";
      # Switching restarts other units; this one must not be restarted.
      RemainAfterExit = true;
    };
    restartIfChanged = false;
    script = ''
      ref=$(sed -n '1s/^#filnix \([^ ]*\)$/\1/p' /etc/ec2-metadata/user-data 2>/dev/null || true)
      if [ -z "$ref" ]; then
        echo "no #filnix line in the user data"
      else
        echo "switching to $ref"
        nixos-rebuild switch --flake "$ref" --option max-jobs 0 --option builders ""
      fi
      touch /var/lib/filnix-first-switch/done
    '';
  };

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
