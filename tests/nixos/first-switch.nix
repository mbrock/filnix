# The AMI's first boot (nixos/amazon.nix) with `#filnix` user data: the
# filnix-first-switch unit switches to the named system while boot goes on.
# As a oneshot it deadlocked: switch-to-configuration waited for
# multi-user.target's start job, which waited for the unit doing the switch.
# The target here is a system in the store, so the VM needs no network.
{ filnix }:
let
  amazon =
    { lib, ... }:
    {
      imports = [ (import ../../nixos/amazon.nix { inherit filnix; }) ];
      systemd.services.fetch-ec2-metadata.enable = false;
      systemd.services.apply-ec2-data.enable = false;
      systemd.services.growpart.enable = false;
      # The test VM boots without one, and switching would install it.
      boot.loader.grub.enable = lib.mkForce false;
      systemd.services."serial-getty@ttyS0".enable = lib.mkForce false;
    };
in
{
  name = "first-switch";
  nodes.target = {
    imports = [ amazon ];
    environment.etc."filnix-switched".text = "yes";
    # Test nodes leave switch-to-configuration out by default.
    system.switch.enable = true;
    # A new service wanted by multi-user.target, as demo-wiki's are: the
    # switch then starts the target, whose boot start job was still
    # waiting for the unit doing the switch.
    systemd.services.filnix-switched = {
      wantedBy = [ "multi-user.target" ];
      serviceConfig.Type = "oneshot";
      serviceConfig.RemainAfterExit = true;
      script = "true";
    };
  };
  nodes.machine =
    { nodes, ... }:
    {
      imports = [ amazon ];
      virtualisation.additionalPaths = [ nodes.target.system.build.toplevel ];
      environment.etc."ec2-metadata/user-data".text = ''
        #filnix ${nodes.target.system.build.toplevel}
      '';
    };

  testScript =
    { nodes, ... }:
    ''
      machine.start()
      machine.wait_for_unit("multi-user.target")
      machine.wait_until_succeeds("test -e /var/lib/filnix-first-switch/done", timeout=900)
      current = machine.succeed("readlink -f /run/current-system").strip()
      assert current == "${nodes.target.system.build.toplevel}", current
      machine.succeed("test \"$(cat /etc/filnix-switched)\" = yes")
      machine.succeed("systemctl is-active filnix-switched.service")
      machine.succeed("systemctl show -p Result --value filnix-first-switch | grep -qx success")
      # It runs once.
      machine.systemctl("restart filnix-first-switch")
      machine.succeed("journalctl -u filnix-first-switch | grep -q 'switching to'")
      print(machine.succeed("journalctl -u filnix-first-switch -o cat"))
    '';
}
