# nixosConfigurations.demo-wiki (nixos/demo-wiki.nix) in a VM: without the
# EC2 metadata service and Let's Encrypt, which the VM has neither of, so
# lighttpd serves ACME's self-signed certificate.
{ filnix }:
{
  name = "demo-wiki";
  nodes.machine =
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

  testScript = ''
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
  '';
}
