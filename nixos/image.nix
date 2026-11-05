# The base Fil-C NixOS image (nixos/base.nix) and what runs it:
#
#   image   the compressed qcow2, built with native tools
#   vm      `nix run .#nixos-vm`: boots it in QEMU on a copy-on-write
#           overlay, on the serial console, with SSH on localhost:2222
#   check   boots that exact image file with -snapshot and checks from the
#           autologin shell that the userland is Fil-C (image-boot.py)
{
  pkgs,
  config,
}:
let
  image = config.system.build.qcow2;
  # make-disk-image's baseName in nixos/base.nix.
  file = "${image}/filnix-nixos-${config.system.nixos.label}.qcow2";
  qemu = pkgs.qemu_kvm;
in
{
  inherit image;

  vm = pkgs.writeShellApplication {
    name = "filnix-nixos-vm";
    runtimeInputs = [ qemu ];
    text = ''
      # Boot filnix's Fil-C NixOS. Changes go to an overlay on the image,
      # kept in $FILNIX_VM_DISK (default ./filnix-nixos.qcow2); delete it to
      # start over. Ctrl-a x quits QEMU.
      disk=''${FILNIX_VM_DISK:-filnix-nixos.qcow2}
      if [ ! -e "$disk" ]; then
        qemu-img create -q -f qcow2 -F qcow2 -b ${file} "$disk" 8G
        echo "filnix-nixos-vm: created $disk on top of ${file}" >&2
      fi
      accel=()
      if [ -w /dev/kvm ]; then
        accel=(-enable-kvm -cpu host)
      else
        echo "filnix-nixos-vm: no /dev/kvm, so QEMU emulates the CPU; expect a slow boot" >&2
      fi
      echo "filnix-nixos-vm: SSH (keys only) on localhost:''${FILNIX_VM_SSH_PORT:-2222}" >&2
      exec qemu-system-x86_64 "''${accel[@]}" -m "''${FILNIX_VM_MEMORY:-2048}" -smp 2 \
        -drive "file=$disk,if=virtio,format=qcow2" \
        -nic "user,model=virtio-net-pci,hostfwd=tcp:127.0.0.1:''${FILNIX_VM_SSH_PORT:-2222}-:22" \
        -nographic "$@"
    '';
  };

  check =
    pkgs.runCommand "filnix-nixos-image-boot"
      {
        requiredSystemFeatures = [ "kvm" ];
        nativeBuildInputs = [ pkgs.python3 ];
      }
      ''
        python3 ${./image-boot.py} ${qemu}/bin/qemu-system-x86_64 ${file} $out
        rm -f $out/qmp.sock
        du -b ${file} | cut -f1 > $out/image-bytes
      '';
}
