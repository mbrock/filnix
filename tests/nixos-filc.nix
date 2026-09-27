# Boot the Fil-C demo machine and use its Fil-C services.
{ pkgs, filcModule }:
let
  keys = import "${pkgs.path}/nixos/tests/ssh-keys.nix" pkgs;
in
pkgs.testers.runNixOSTest {
  name = "nixos-filc";
  nodes.machine = {
    imports = [
      filcModule
      ../nixos/demo.nix
    ];
    users.users.root.openssh.authorizedKeys.keys = [ keys.snakeOilPublicKey ];
    virtualisation.memorySize = 4096;
    # The VM has no network.
    nix.settings.substituters = pkgs.lib.mkForce [ ];
  };

  testScript = ''
    machine.wait_for_unit("sshd.service")
    machine.wait_for_unit("lighttpd.service")
    machine.wait_for_unit("unbound.service")
    machine.wait_for_unit("nix-daemon.socket")

    with subtest("the services run Fil-C builds"):
        for unit, exe in [("sshd", "sshd"), ("lighttpd", "lighttpd"), ("unbound", "unbound")]:
            pid = machine.succeed(f"systemctl show -p MainPID --value {unit}").strip()
            machine.succeed(f"grep -q libpizlo /proc/{pid}/maps")
        print(machine.succeed("filc-status"))

    with subtest("ssh into the Fil-C sshd and its Fil-C login shell"):
        machine.succeed("install -m 600 ${keys.snakeOilPrivateKey} /tmp/key")
        out = machine.succeed(
            "ssh -i /tmp/key -o StrictHostKeyChecking=no root@localhost "
            "'echo $BASH_VERSION; grep -c libpizlo /proc/$$/maps'"
        )
        assert int(out.split()[-1]) > 0, out

    with subtest("Fil-C tools, lighttpd and unbound"):
        machine.succeed("curl -s http://localhost/ | grep -q 'Fil-C lighttpd'")
        machine.succeed("grep -q libpizlo $(readlink -f $(command -v curl))")
        machine.succeed("python3 -c 'import sqlite3; print(sqlite3.connect(\":memory:\").execute(\"select 6*7\").fetchone())'")
        machine.succeed("unbound-checkconf")

    with subtest("Fil-C Nix evaluates and builds"):
        machine.succeed("nix-instantiate --eval -E '6 * 7' | grep -q 42")
        machine.succeed(
            "nix-build -E 'derivation { name = \"hi\"; system = builtins.currentSystem; "
            "builder = \"/bin/sh\"; args = [ \"-c\" \"echo hi > $out\" ]; }' "
            "--no-out-link | xargs cat | grep -q hi"
        )
  '';
}
