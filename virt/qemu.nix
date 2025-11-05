{
  pkgs,
  ports,
  world-pkgs,
}:

let
  common = import ./common.nix { inherit pkgs ports; };
  inherit (common) ghostty-terminfo dank-bashrc lighttpd-demo;

  # Minimal headless QEMU without GUI dependencies
  qemu-headless = (
    pkgs.qemu_kvm.override {
      hostCpuOnly = true; # Only build for host CPU architecture
      gtkSupport = false;
      sdlSupport = false;
      spiceSupport = false;
      ncursesSupport = false;
      smartcardSupport = false;
      usbredirSupport = false;
      vncSupport = false;
      openGLSupport = false;
      virglSupport = false;
      jackSupport = false;
      pulseSupport = false;
      pipewireSupport = false;
      alsaSupport = false;
      tpmSupport = false;
      smbdSupport = false;
      libiscsiSupport = false;
      glusterfsSupport = false;
      cephSupport = false;
    }
  );

  core =
    import ./core.nix
      {
        inherit
          pkgs
          ports
          world-pkgs
          dank-bashrc
          ghostty-terminfo
          lighttpd-demo
          ;
      }
      {
        consoleDevice = "/dev/ttyS0";
        mountFilesystems = true; # QEMU needs to mount everything
      };

  inherit (core) env mkRootfsScript;

  kernel = pkgs.linuxPackages_latest.kernel.override {
    ignoreConfigErrors = true;
    autoModules = false;

    structuredExtraConfig = with pkgs.lib.kernel; {
      VIRTIO = yes;
      VIRTIO_MENU = yes;
      VIRTIO_PCI = yes;
      VIRTIO_PCI_LIB = yes;
      VIRTIO_BLK = yes;
      MODVERSIONS = pkgs.lib.mkForce no;
    };
  };

  # Script that builds the rootfs and creates a disk image
  imageBuilder = pkgs.writeShellScript "build-filc-qemu-image" ''
    set -euo pipefail

    output="''${1:-filc-rootfs.img}"

    echo "Building Fil-C QEMU disk image: $output"

    # Create temporary directory for rootfs
    workdir=$(mktemp -d)
    trap 'chmod -R +w "$workdir" 2>/dev/null || true; rm -rf "$workdir"' EXIT

    rootfs="$workdir/rootfs"
    mkdir -p "$rootfs"

    # Build rootfs using shared script
    echo "Assembling rootfs..."
    ${mkRootfsScript "$rootfs"}

    # Calculate actual size needed (with 20% overhead)
    actual_size=$(${pkgs.coreutils}/bin/du -sb "$rootfs" | ${pkgs.coreutils}/bin/cut -f1)
    size_with_overhead=$((actual_size * 120 / 100))
    echo "Rootfs size: $actual_size bytes (allocating $size_with_overhead bytes with overhead)"

    # Create raw disk image
    echo "Creating raw ext4 disk image..."
    ${pkgs.coreutils}/bin/truncate -s "$size_with_overhead" "$output"

    # Format as ext4
    ${pkgs.e2fsprogs}/bin/mkfs.ext4 -q -L filc-root "$output"

    # Mount and copy rootfs
    echo "Copying rootfs to disk..."
    mnt="$workdir/mnt"
    mkdir -p "$mnt"
    sudo ${pkgs.util-linux}/bin/mount -o loop "$output" "$mnt"
    trap 'sudo ${pkgs.util-linux}/bin/umount "$mnt" 2>/dev/null || true; chmod -R +w "$workdir" 2>/dev/null || true; rm -rf "$workdir"' EXIT

    sudo ${pkgs.rsync}/bin/rsync -a "$rootfs/" "$mnt/"
    sudo ${pkgs.util-linux}/bin/umount "$mnt"

    echo "Disk image created: $output"
    ${pkgs.coreutils}/bin/ls -lh "$output"
    echo
    echo "To compress for distribution:"
    echo "  ${qemu-headless}/bin/qemu-img convert -f raw -O qcow2 -c $output ''${output%.img}.qcow2"
  '';

in
pkgs.buildEnv {
  name = "filc-qemu";
  paths = [
    (pkgs.writeShellScriptBin "build-filc-qemu-image" ''
      exec ${imageBuilder} "$@"
    '')
    (pkgs.writeShellScriptBin "run-filc-qemu" ''
      set -euo pipefail

      disk="''${1:-/tmp/filc.img}"
      ${imageBuilder} "$disk"

      # Auto-detect format from extension
      format="raw"
      case "$disk" in
        *.qcow2) format="qcow2" ;;
        *.img|*.raw) format="raw" ;;
      esac

      qemu=${qemu-headless}/bin/qemu-system-x86_64
      kernel=${kernel}/bzImage

      accelFlags="-cpu max"
      if [ -e /dev/kvm ] && [ -r /dev/kvm ] && [ -w /dev/kvm ]; then
        accelFlags="-enable-kvm -cpu host"
      else
        echo "warning: /dev/kvm unavailable, falling back to TCG (-cpu max)" >&2
        echo "         Fil-C runtime may require modern CPU features; enable KVM if possible." >&2
      fi

      echo "Starting Fil-C QEMU (disk: $disk, format: $format)..."
      exec "$qemu" \
        -m 512 \
        -kernel "$kernel" \
        -drive file="$disk",if=virtio,format="$format" \
        -append "console=ttyS0 root=/dev/vda rootwait init=/bin/runit-init panic=-1 oops=panic earlyprintk=serial,ttyS0,115200" \
        -nographic \
        -no-reboot \
        $accelFlags
    '')
  ];
  pathsToLink = [ "/bin" ];
}
