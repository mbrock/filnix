# Boot a filnix NixOS image in QEMU on its serial console, as a user would,
# and check from the autologin shell that the userland is Fil-C.
#
#   image-boot.py QEMU IMAGE OUTDIR
#
# QEMU runs with -snapshot, so the image file is not changed. OUTDIR gets the
# serial log and a screenshot of the graphical console (tty1).
import json
import os
import re
import select
import socket
import subprocess
import sys
import time

qemu, image, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)
log = open(os.path.join(out, "serial.log"), "wb")
qmp_path = os.path.join(out, "qmp.sock")

accel = ["-enable-kvm", "-cpu", "host"] if os.access("/dev/kvm", os.W_OK) else []
vm = subprocess.Popen(
    [qemu, *accel, "-m", "2048", "-smp", "2", "-snapshot",
     "-drive", f"file={image},if=virtio,format={'vpc' if image.endswith('.vhd') else 'qcow2'}",
     "-nic", "user,model=virtio-net-pci",
     "-serial", "stdio", "-display", "none", "-vga", "std",
     "-qmp", f"unix:{qmp_path},server=on,wait=off"],
    stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
)
seen = b""


def expect(pattern, timeout):
    """Read the serial line until `pattern` matches what came since the last match."""
    global seen
    deadline = time.time() + timeout
    while True:
        m = re.search(pattern.encode(), seen, re.S)
        if m:
            seen = seen[m.end():]
            return m
        left = deadline - time.time()
        if left <= 0 or vm.poll() is not None:
            sys.exit(f"timed out waiting for {pattern!r}; last output:\n"
                     + seen[-2000:].decode(errors="replace"))
        r, _, _ = select.select([vm.stdout], [], [], min(left, 1))
        if r:
            chunk = os.read(vm.stdout.fileno(), 65536)
            log.write(chunk)
            log.flush()
            sys.stdout.write(chunk.decode(errors="replace"))
            sys.stdout.flush()
            seen += chunk


def run(command, timeout=120):
    """Run `command` in the serial shell and return its output and status."""
    vm.stdin.write(f"{command}; echo \"@@rc=$?@@\"\n".encode())
    vm.stdin.flush()
    m = expect(r"(.*?)@@rc=(\d+)@@", timeout)
    output = m.group(1).decode(errors="replace").replace("\r", "").strip()
    return output, int(m.group(2))


def check(command, timeout=120):
    output, rc = run(command, timeout)
    assert rc == 0, f"{command} exited {rc}"
    return output


def screenshot(name):
    s = socket.socket(socket.AF_UNIX)
    s.connect(qmp_path)
    f = s.makefile("rw")
    f.readline()
    for cmd in [{"execute": "qmp_capabilities"},
                {"execute": "screendump",
                 "arguments": {"filename": os.path.join(out, name), "format": "png"}}]:
        f.write(json.dumps(cmd) + "\n")
        f.flush()
        while "return" not in (reply := json.loads(f.readline())) and "error" not in reply:
            pass
        assert "error" not in reply, reply
    s.close()


try:
    started = time.time()
    # getty logs demo in on the serial line; Bash then prints its prompt.
    expect(r"demo@filc[^\n]*\$", 600)
    print(f"\n== logged in after {time.time() - started:.0f} s", flush=True)
    # Prompts and echoes after this go to the log, not into matches.
    check("stty -echo; PS1=''")

    exe = check("sudo readlink /proc/1/exe")
    assert "gnufilc0" in exe, f"PID 1 is not a Fil-C build: {exe}"
    check("sudo grep -q libpizlo /proc/1/maps")
    shell = check("readlink /proc/$$/exe")
    assert "gnufilc0" in shell, f"the login shell is not a Fil-C build: {shell}"
    check("grep -q libpizlo /proc/$$/maps")

    # Wait until the services are up, then the inverse check.
    check("systemctl is-system-running --wait >/dev/null || true", 300)
    print(check("systemctl --failed --no-legend"))
    check("test -z \"$(systemctl --failed --no-legend)\"")
    print(check("sudo filc-ps"))

    # sshd runs, Fil-C, and takes keys only.
    sshd = check("sudo sshd -T -f /etc/ssh/sshd_config 2>&1").lower().split("\n")
    assert "passwordauthentication no" in sshd and "kbdinteractiveauthentication no" in sshd
    check("sudo grep -q libpizlo /proc/$(systemctl show -p MainPID --value sshd)/maps")

    # The pinned flake and the binary cache.
    print(check("cat /etc/nixos/flake.nix"))
    check("grep -q 'github:mbrock/filnix/' /etc/nixos/flake.nix")
    check("nix config show substituters | grep -q filc.cachix.org")

    # The graphical console has its own autologin; show the check there too.
    check("sudo sh -c '{ echo sudo filc-ps; filc-ps | tail -n 14; } > /dev/tty1'")
    time.sleep(1)
    screenshot("console.png")
    print(f"== passed after {time.time() - started:.0f} s", flush=True)
finally:
    vm.kill()
    vm.wait()
