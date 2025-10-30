{ base, ports, filc-sysroot }:

let
  lib = base.lib;

  runit = ports.runit;
  busybox = ports.busybox;
  bash = ports.dash;
  runtimeLibs = filc-sysroot;

  initrd = base.runCommand "filc-runit-initrd" {
    buildInputs = with base; [ cpio gzip coreutils findutils ];
    passthru = {
      inherit runit busybox runtimeLibs;
    };
  } ''
    set -euo pipefail
    set -x

    root=$PWD/root
    mkdir -p "$root"

    install -d "$root"/{bin,sbin,etc/runit,etc/service,var/log,run,proc,sys,dev,tmp,root,nix/store}

    copyStorePath() {
      local src="$1"
      local dst="$root$src"
      mkdir -p "$(dirname "$dst")"
      cp -a --no-preserve=ownership "$src" "$dst"
    }

    copyStorePath ${runit}
    copyStorePath ${busybox}
    copyStorePath ${runtimeLibs}
    copyStorePath ${bash}

    ln -s ../bin/runit "$root/sbin/runit"

    for exe in runit runit-init runsv runsvdir runsvchdir chpst sv svlogd utmpset; do
      ln -s ${runit}/bin/$exe "$root/bin/$exe"
    done

    ln -s ${busybox}/bin/busybox "$root/bin/busybox"
    ln -s ${bash}/bin/dash "$root/bin/bash"

    for applet in sh ls cat echo printf dmesg mount umount mkdir ln setsid date sleep ps; do
      ln -s busybox "$root/bin/$applet"
    done

    cat > "$root/etc/runit/1" <<'EOF'
#!/bin/sh
PATH=/bin
export PATH
bb=/bin/busybox

$bb mkdir -p /proc /sys /run /dev /etc/service /var/log
$bb mount -t proc proc /proc
$bb mount -t sysfs sysfs /sys
$bb mount -t devtmpfs devtmpfs /dev
$bb mount -t tmpfs tmpfs /run
if [ -e /dev/ttyS0 ]; then
  $bb ln -sf /dev/ttyS0 /dev/console
fi
$bb hostname filc-runit
echo "[stage1] Fil-C runit environment ready"
exit 0
EOF

    cat > "$root/etc/runit/2" <<'EOF'
#!/bin/sh
PATH=/bin
export PATH
echo "[stage2] launching runsvdir on /etc/service"
exec /bin/runsvdir -P /etc/service
EOF

    cat > "$root/etc/runit/3" <<'EOF'
#!/bin/sh
PATH=/bin
export PATH
bb=/bin/busybox
$bb echo "[stage3] shutdown hooks running"
for target in /run /proc /sys /dev; do
  $bb umount "$target" 2>/dev/null || true
done
exit 0
EOF

    install -d "$root/etc/service/console"
    cat > "$root/etc/service/console/run" <<'EOF'
#!/bin/sh
PATH=/bin
export PATH
exec /bin/busybox setsid -w /bin/bash -l </dev/ttyS0 >/dev/ttyS0 2>&1
EOF

    install -d "$root/etc/service/banner"
    cat > "$root/etc/service/banner/run" <<'EOF'
#!/bin/sh
PATH=/bin
export PATH
bb=/bin/busybox
while true; do
  ts=$($bb date -Iseconds)
  $bb printf '[banner] Fil-C runit alive @ %s\n' "$ts"
  $bb sleep 30
done
EOF

    chmod +x "$root/etc/runit/"{1,2,3}
    chmod +x "$root/etc/service/console/run"
    chmod +x "$root/etc/service/banner/run"

    mkdir -p "$out"
    (cd "$root" && find . -print0 | LC_ALL=C sort -z | cpio --null -o --format=newc | gzip -9) > "$out/initrd.cpio.gz"
  '';

in {
  inherit initrd runit busybox;

  runner = base.writeShellScriptBin "run-filc-runit-qemu" ''
    set -euo pipefail

    qemu=${base.qemu_kvm}/bin/qemu-system-x86_64
    kernel=${base.linuxPackages_latest.kernel}/bzImage

    accelFlags="-cpu max"
    if [ -e /dev/kvm ] && [ -r /dev/kvm ] && [ -w /dev/kvm ]; then
      accelFlags="-enable-kvm -cpu host"
    else
      echo "warning: /dev/kvm unavailable, falling back to TCG (-cpu max)" >&2
      echo "         Fil-C runtime may require modern CPU features; enable KVM if possible." >&2
    fi

    exec "$qemu" \
      -m 512 \
      -kernel "$kernel" \
      -initrd ${initrd}/initrd.cpio.gz \
      -append "console=ttyS0 rdinit=/bin/runit-init panic=-1 oops=panic" \
      -nographic \
      -no-reboot \
      $accelFlags
  '';
}
