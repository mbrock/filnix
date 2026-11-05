# A NixOS VM whose whole userland is Fil-C (nixosModules.default): it boots,
# a user logs in on the console, PID 1 and the main services map the Fil-C
# runtime, and filc-ps finds no native process but the allowed exceptions.
#
#   nix build .#nixosTests.userland
{
  pkgs,
  filcModule,
}:
let
  # A CA the machine trusts through security.pki, and a localhost
  # certificate it signed, for the HTTPS subtest.
  tls =
    pkgs.runCommand "userland-test-tls" { nativeBuildInputs = [ pkgs.openssl ]; }
      ''
        mkdir $out && cd $out
        openssl req -x509 -newkey rsa:2048 -nodes -days 36500 -subj /CN=test-ca \
          -keyout ca.key -out ca.crt
        openssl req -newkey rsa:2048 -nodes -subj /CN=localhost -keyout key.pem -out req.csr
        printf 'subjectAltName=DNS:localhost\n' > ext
        openssl x509 -req -in req.csr -CA ca.crt -CAkey ca.key -CAcreateserial \
          -days 36500 -extfile ext -out cert.pem
      '';
in
pkgs.testers.runNixOSTest {
  name = "filc-userland";
  # The module chooses the package set.
  node.pkgsReadOnly = false;

  nodes.machine =
    { lib, pkgs, ... }:
    {
      imports = [ filcModule ];
      filc.enable = true;

      virtualisation.memorySize = 2048;
      users.users.alice = {
        isNormalUser = true;
        password = "foobar";
      };
      services.openssh.enable = true;
      # Its unit sets IOSchedulingClass (see the test below).
      services.logrotate.enable = true;
      # The test driver talks to the VM over its backdoor, not the guest
      # agent, and the agent comes from a QEMU build Fil-C cannot do yet.
      services.qemuGuest.enable = lib.mkForce false;

      # OpenSSL finds the system's CAs with no SSL_CERT_FILE: the unit
      # runs curl with an empty environment against a local TLS server.
      security.pki.certificateFiles = [ "${tls}/ca.crt" ];
      systemd.services.tls-server = {
        wantedBy = [ "multi-user.target" ];
        serviceConfig.ExecStart = "${pkgs.openssl.bin}/bin/openssl s_server -accept 4433 -cert ${tls}/cert.pem -key ${tls}/key.pem -www";
      };
      systemd.services.https-fetch.serviceConfig = {
        Type = "oneshot";
        ExecStart = "${pkgs.coreutils}/bin/env -i ${pkgs.curl}/bin/curl -fsS -o /dev/null https://localhost:4433/";
      };
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

    with subtest("a unit with an IO scheduling class runs"):
        # logrotate sets IOSchedulingClass; ioprio_set has no Fil-C wrapper.
        machine.succeed("systemctl start logrotate.service")

    with subtest("a unit with no environment fetches over HTTPS"):
        machine.wait_for_open_port(4433)
        machine.succeed("systemctl start https-fetch.service")

    with subtest("no native process but the allowed exceptions"):
        print(machine.succeed("filc-ps"))
        # The rule has teeth: a native program outside the exceptions fails it.
        machine.succeed("${pkgs.coreutils}/bin/sleep 600 >/dev/null 2>&1 &")
        out = machine.fail("filc-ps")
        assert "not an allowed native exception" in out, out
  '';
}
