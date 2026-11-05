# A NixOS VM whose whole userland is Fil-C (nixosModules.default): it boots,
# a user logs in on the console, PID 1 and the main services map the Fil-C
# runtime, and filc-ps finds no native process but the allowed exceptions.
#
#   nix build .#nixosTests.userland
{
  pkgs,
  filcModule,
}:
pkgs.testers.runNixOSTest {
  name = "filc-userland";
  # The module chooses the package set.
  node.pkgsReadOnly = false;

  nodes.machine =
    { lib, ... }:
    {
      imports = [ filcModule ];
      filc.enable = true;

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

    with subtest("mount(8) mounts"):
        # With a list of types (or a helper such as mount.davfs), libmount
        # probes the new mount API with fsopen(NULL), which used to stop it.
        machine.succeed("mkdir -p /mnt/t && mount -t tmpfs,ramfs none /mnt/t && findmnt /mnt/t && umount /mnt/t")

    with subtest("no native process but the allowed exceptions"):
        print(machine.succeed("filc-ps"))
        # The rule has teeth: a native program outside the exceptions fails it.
        machine.succeed("${pkgs.coreutils}/bin/sleep 600 >/dev/null 2>&1 &")
        out = machine.fail("filc-ps")
        assert "not an allowed native exception" in out, out
  '';
}
