{ pkgs, ports, filcc, world-pkgs }:
rec {
  filc-nspawn = import ./virt/nspawn.nix {
    inherit pkgs ports filcc;
    inherit world-pkgs;
  };

  filc-qemu = import ./virt/qemu.nix {
    inherit pkgs ports filcc;
    inherit world-pkgs;
  };

  filc-docker = import ./virt/docker.nix {
    inherit pkgs ports filcc;
    inherit world-pkgs;
  };

  apps = {
    run-filc-docker = {
      type = "app";
      program = "${filc-docker}";
    };

    run-filc-sandbox = {
      type = "app";
      program = "${pkgs.writeShellScript "filc-sandbox" ''
        exec sudo systemd-nspawn --ephemeral \
          -M filbox \
          -D ${filc-nspawn} /bin/runit-init
      ''}";
    };

    run-filc-qemu = {
      type = "app";
      program = "${filc-qemu}/bin/run-filc-qemu";
    };

    build-filc-qemu-image = {
      type = "app";
      program = "${filc-qemu}/bin/build-filc-qemu-image";
    };
  };
}
