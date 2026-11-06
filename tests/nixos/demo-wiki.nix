# nixosConfigurations.demo-wiki (nixos/demo-wiki.nix) in a VM: without the
# EC2 metadata service and Let's Encrypt, which the VM has neither of, so
# lighttpd serves ACME's self-signed certificate.
{ filnix }:
let
  wiki =
    { lib, ... }:
    {
      imports = [ (import ../../nixos/demo-wiki.nix { inherit filnix; }) ];
      virtualisation.memorySize = 4096;
      systemd.services.fetch-ec2-metadata.enable = false;
      systemd.services.apply-ec2-data.enable = false;
      # The test VM's disk has no partition to grow.
      systemd.services.growpart.enable = false;
      systemd.services."acme-order-renew-filc.less.rest".enable = false;
      systemd.timers.filnix-update.enable = false;
      # The test driver has the serial line.
      systemd.services."serial-getty@ttyS0".enable = lib.mkForce false;
      networking.hosts."127.0.0.1" = [ "filc.less.rest" ];
    };
in
{
  name = "demo-wiki";
  # The system filnix-update switches to: another build of this one, whose
  # filnix-update unit differs, as each release's does.
  nodes.target =
    { lib, ... }:
    {
      imports = [ wiki ];
      system.switch.enable = true;
      # The test VM boots without one, and switching would install it.
      boot.loader.grub.enable = lib.mkForce false;
      systemd.services.filnix-update.environment.RELEASE = "next";
    };
  nodes.machine =
    { lib, nodes, ... }:
    {
      imports = [ wiki ];
      virtualisation.additionalPaths = [ nodes.target.system.build.toplevel ];
      # filnix-update as on the box, switching to the target instead of a
      # release from GitHub, which the VM cannot reach.
      systemd.services.filnix-update.script = lib.mkForce ''
        nixos-rebuild switch --no-reexec --store-path ${nodes.target.system.build.toplevel} \
          --option max-jobs 0 --option builders ""
        echo next > /var/lib/filnix-update/tag
        systemctl start --no-block filc-status.service
      '';
    };

  testScript =
    { nodes, ... }:
    ''
      machine.wait_for_unit("lighttpd.service")
      machine.wait_for_unit("phpfpm-mediawiki.service")
      machine.wait_for_open_port(443)

      with subtest("HTTP redirects to HTTPS, which serves the wiki"):
          out = machine.succeed("curl -sS -o /dev/null -w '%{http_code} %{redirect_url}' http://filc.less.rest/index.php")
          assert out.startswith("301 https://filc.less.rest/"), out
          page = machine.succeed("curl -fsSk https://filc.less.rest/index.php?title=Main_Page")
          assert "Fil-C wiki" in page, page[:500]

      with subtest("anonymous users cannot edit or create accounts"):
          edit = machine.succeed("curl -fsSk 'https://filc.less.rest/index.php?title=Main_Page&action=edit'")
          assert "wpTextbox1" not in edit or "readonly" in edit, "the edit form is open"
          signup = machine.succeed("curl -fsSk 'https://filc.less.rest/index.php?title=Special:CreateAccount'")
          assert "wpCreateaccount" not in signup, "account creation is open"

      with subtest("the status page lists filc-ps"):
          machine.systemctl("start filc-status.service")
          status = machine.succeed("curl -fsSk https://filc.less.rest/status/")
          print(status)
          assert "0 not allowed" in status, status

      with subtest("lighttpd and php-fpm are Fil-C"):
          for unit in ["lighttpd", "phpfpm-mediawiki"]:
              pid = machine.succeed(f"systemctl show -p MainPID --value {unit}").strip()
              machine.succeed(f"grep -q libpizlo /proc/{pid}/maps")

      with subtest("filnix-update survives the switch it runs"):
          # Its unit changes in the switch; restarting it there killed it
          # before it wrote the tag (filc.less.rest, v2026.11.06).
          machine.succeed("systemctl start filnix-update.service")
          current = machine.succeed("readlink -f /run/current-system").strip()
          assert current == "${nodes.target.system.build.toplevel}", current
          machine.succeed("test \"$(cat /var/lib/filnix-update/tag)\" = next")
          machine.succeed("systemctl show -p Result --value filnix-update | grep -qx success")
          machine.wait_until_succeeds("grep -q 'filnix-update: next' /var/lib/filc-status/index.txt")
          print(machine.succeed("head -4 /var/lib/filc-status/index.txt"))
    '';
}
