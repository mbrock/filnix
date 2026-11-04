# Boot the example finix machine (finix/demo.nix) with finix's own VM test
# driver and check that its userland is Fil-C: PID 1, the shells and sshd map
# the Fil-C runtime, an ssh login gets a Fil-C shell, no running process is
# native except the Nix daemon, and every native ELF file in the closure
# belongs to one of the expected exceptions (finix/filc-audit.sh).
{
  pkgs,
  finix,
  filnix,
}:
let
  inherit (pkgs) lib;
  # finix's driver adds finit_machine.py to the NixOS test driver, for a
  # FinitMachine class the driver never instantiates; it imports
  # test_driver.duration, which this Nixpkgs' driver does not have yet, and
  # fails the driver's type check. Leave it out.
  finixSrc = pkgs.applyPatches {
    name = "finix-source";
    src = finix;
    postPatch = "sed -i '/finit_machine.py/d' tests/lib/driver.nix";
  };
  testLib = import "${finixSrc}/tests/lib" { inherit pkgs lib; };
  audit = filnix.packages.${pkgs.stdenv.hostPlatform.system}.filc-audit;
in
testLib.mkTest {
  name = "filc-userland";

  nodes.machine =
    { config, lib, ... }:
    {
      imports = [
        filnix.finixModules.filc-userland
        ./demo.nix
      ];
      filc.userland.system = pkgs.stdenv.hostPlatform.system;
      # The test library sets the native package set; the module replaces it.
      nixpkgs.pkgs = lib.mkForce config.filc.userland.packages;
      # finix's test network brings eth0 up with ifupdown-ng (Fil-C, with
      # libbsd). dhcpcd also runs; it gets no lease, as there is no server.
    };

  testScript =
    { nodes }:
    let
      cfg = nodes.machine.config;
      closure = pkgs.closureInfo { rootPaths = [ cfg.system.topLevel ]; };
      # The packages finix/userland.nix takes from the native set, with their
      # closures. Fil-C's glibc keeps native bash for the shebangs of its
      # scripts (ldd and friends); the setuid wrappers are added by name below.
      expectedNative = pkgs.closureInfo {
        rootPaths = with cfg.filc.userland.packages; [
          nix
          userborn
          pkgsBuildBuild.bashNonInteractive
        ];
      };
    in
    ''
      import subprocess

      machine.start()
      machine.wait_for_console_text("entering runlevel 2")
      machine.wait_until_succeeds("pgrep -x sshd", timeout=600)

      def maps_pizlo(pid):
          return int(machine.succeed(f"grep -c libpizlo /proc/{pid}/maps || true").strip() or 0) > 0

      with subtest("no finit service crashed"):
          # A crashing service restarts for a while before finit gives up.
          machine.sleep(15)
          status = machine.succeed("initctl status")
          print(status)
          assert "crashed" not in status, status
          for service in ["dhcpcd", "keventd", "sshd", "syslogd"]:
              row = next(l for l in status.splitlines() if f" {service} " in l)
              assert " running " in row, row

      with subtest("ifupdown-ng configured eth0"):
          addr = machine.succeed("ip -4 -o addr show dev eth0")
          print(addr)
          assert "${cfg.testing.network.ip}/24" in addr, addr

      with subtest("PID 1, the shell and sshd are Fil-C"):
          print(machine.succeed("readlink /proc/1/exe"))
          assert maps_pizlo(1), "finit does not map libpizlo"
          assert maps_pizlo("$$"), "the test shell does not map libpizlo"
          sshd = machine.succeed("pgrep -o -x sshd").strip()
          print(machine.succeed(f"readlink /proc/{sshd}/exe"))
          assert maps_pizlo(sshd), "sshd does not map libpizlo"

      with subtest("an ssh login gets a Fil-C shell"):
          machine.succeed(
              "mkdir -p -m 700 /root/.ssh",
              "ssh-keygen -q -t ed25519 -N ''' -f /root/.ssh/id_ed25519",
              "cp /root/.ssh/id_ed25519.pub /root/.ssh/authorized_keys",
          )
          out = machine.succeed(
              "ssh -n -o StrictHostKeyChecking=no -o BatchMode=yes root@localhost "
              "'echo $BASH_VERSION; readlink /proc/$$/exe; grep -c libpizlo /proc/$$/maps'"
          )
          print(out)
          assert int(out.split()[-1]) > 0, out

      with subtest("no running process is native but the Nix daemon"):
          census = machine.succeed(
              "for d in /proc/[0-9]*; do "
              "  grep -q . $d/maps 2>/dev/null || continue; "  # kernel threads map nothing
              "  if grep -q libpizlo $d/maps; then k=Fil-C; else k=native; fi; "
              "  echo \"$k ''${d#/proc/} $(readlink $d/exe)\"; "
              "done"
          )
          print(census)
          rows = [(line.split(" ", 2) + [""])[:3] for line in census.splitlines() if line]
          native = [r for r in rows if r[0] == "native"]
          filc = {r[2].rsplit("/", 1)[-1] for r in rows if r[0] == "Fil-C"}
          assert {"finit", "sshd", "bash"} <= filc, filc
          unexpected = [r for r in native if not r[2].endswith("/bin/nix-daemon") and not r[2].endswith("/bin/nix")]
          assert not unexpected, f"native processes: {unexpected}"

      with subtest("native ELF files belong to the expected exceptions"):
          allow = "${expectedNative}/store-paths"
          with open("${closure}/store-paths") as f:
              wrappers = [p.strip() for p in f if "-security-wrapper-" in p]
          with open("allow", "w") as f:
              f.write(open(allow).read() + "\n".join(wrappers) + "\n")
          result = subprocess.run(
              ["${audit}/bin/filc-audit", "--paths", "${closure}/store-paths", "--allow", "allow"],
              capture_output=True, text=True,
          )
          print(result.stdout, result.stderr)
          assert result.returncode == 0, "native files outside the expected exceptions"

      machine.shutdown()
    '';
}
