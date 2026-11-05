# A NixOS VM whose whole userland is Fil-C (nixos/userland.nix): it boots,
# a user logs in on the console, and PID 1 and the main services map the
# Fil-C runtime.
#
#   nix build .#nixosTests.userland
{
  pkgs,
  userlandModule,
}:
pkgs.testers.runNixOSTest {
  name = "filc-userland";
  # The module chooses the package set.
  node.pkgsReadOnly = false;

  nodes.machine =
    { lib, ... }:
    {
      imports = [ userlandModule ];
      filc.userland.enable = true;

      virtualisation.memorySize = 2048;
      users.users.alice = {
        isNormalUser = true;
        password = "foobar";
      };
      services.openssh.enable = true;
      # The test driver talks to the VM over its backdoor, not the guest
      # agent, and the agent comes from a QEMU build Fil-C cannot do yet.
      services.qemuGuest.enable = lib.mkForce false;
    };

  testScript = ''
    machine.wait_for_unit("multi-user.target")

    with subtest("log in on the console"):
        machine.wait_until_tty_matches("1", "login: ")
        machine.send_chars("alice\n")
        machine.wait_until_tty_matches("1", "Password: ")
        machine.send_chars("foobar\n")
        machine.wait_until_succeeds("pgrep -u alice bash")
        machine.send_chars("echo $((6*7)) > /tmp/answer\n")
        machine.wait_for_file("/tmp/answer")
        assert machine.succeed("cat /tmp/answer").strip() == "42"

    with subtest("PID 1 and the main services run Fil-C builds"):
        procs = {
            "systemd (PID 1)": "1",
            "journald": "$(systemctl show -p MainPID --value systemd-journald)",
            "udevd": "$(systemctl show -p MainPID --value systemd-udevd)",
            "logind": "$(systemctl show -p MainPID --value systemd-logind)",
            "dbus": "$(systemctl show -p MainPID --value dbus)",
            "sshd": "$(systemctl show -p MainPID --value sshd)",
            "alice's bash": "$(pgrep -u alice -x bash | head -1)",
        }
        for what, pid in procs.items():
            pid = machine.succeed(f"echo {pid}").strip()
            assert pid not in ("", "0"), f"{what} is not running"
            exe = machine.succeed(f"readlink -f /proc/{pid}/exe").strip()
            machine.succeed(f"grep -q libpizlo /proc/{pid}/maps")
            print("Fil-C %-16s %6s %s" % (what, pid, exe), flush=True)
  '';
}
