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
  # everything (scripts/launch-demo-wiki uses it). `#filnix /nix/store/...`
  # switches to a system already in the store or a cache. Other user data
  # is ignored.
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
      # Not oneshot: multi-user.target is ordered after the units it wants,
      # so a oneshot would hold the target's start job until the switch
      # ends, while switch-to-configuration waits for that same job. A
      # simple service counts as started at once.
      Type = "simple";
      StateDirectory = "filnix-first-switch";
    };
    # Switching must not stop or restart the unit that runs it.
    restartIfChanged = false;
    script = ''
      ref=$(sed -n '1s/^#filnix \([^ ]*\)$/\1/p' /etc/ec2-metadata/user-data 2>/dev/null || true)
      set -- --option max-jobs 0 --option builders ""
      rc=0
      case $ref in
        "") echo "no #filnix line in the user data" ;;
        /nix/store/*)
          echo "switching to $ref"
          nix-store --realise "$ref" "$@"
          # There is no flake to take a newer nixos-rebuild from.
          nixos-rebuild switch --no-reexec --store-path "$ref" "$@" || rc=$?
          ;;
        *)
          echo "switching to $ref"
          nixos-rebuild switch --flake "$ref" "$@" || rc=$?
          ;;
      esac
      # 4: the new system is active but some of its units failed, such as
      # ACME before DNS points here. Switching again would not help them.
      if [ "$rc" = 4 ]; then
        echo "switched, but these units failed:"
        systemctl --failed --no-legend --plain
      elif [ "$rc" != 0 ]; then
        exit "$rc"
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
