{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/c8aa8cc00a5cb57fada0851a038d35c08a36a2bb";
    # Modified nixpkgs with Fil-C cross-compilation support
    nixpkgs-filc.url = "path:/home/mbrock/nixpkgs";
    nixpkgs-filc.flake = false;
  };

  outputs =
    {
      self,
      nixpkgs,
      nixpkgs-filc,
      ...
    }:
    let
      system = "x86_64-linux";
      base = import nixpkgs { inherit system; };

      # Import helper libraries and sources
      lib = import ./lib { inherit base; };
      sources = import ./lib/sources.nix { inherit base; };

      # Build the complete Fil-C compiler with all dependencies
      filc = import ./build-filc.nix { inherit base lib sources; };

      # Build toolchain components directly
      filc-binutils = import ./toolchain/binutils.nix { inherit base; };

      filc-sysroot = import ./toolchain/sysroot.nix { inherit base lib filc; };

      toolchain = import ./toolchain/wrappers.nix {
        inherit
          base
          lib
          filc
          filc-sysroot
          filc-binutils
          ;
      };

      ports = import ./ports.nix {
        inherit base;
        inherit (toolchain)
          filenv
          withFilC
          fix
          filcc
          ;
        filc-src = sources.filc0-src;
      };

      # Build shells
      shell-world = import ./shells/world.nix { inherit base toolchain ports; };
      shell-wasm3-cve = import ./shells/wasm3-cve-test.nix { inherit base ports; };

      # Virtualization variants (nspawn, qemu, docker)
      virt-nspawn = import ./virt/nspawn.nix {
        inherit base ports;
        world-pkgs = shell-world.world-pkgs;
      };
      virt-qemu = import ./virt/qemu.nix {
        inherit base ports;
        world-pkgs = shell-world.world-pkgs;
      };
      virt-docker = import ./virt/docker.nix {
        inherit base ports;
        world-pkgs = shell-world.world-pkgs;
      };

    in
    {
      lib.${system}.queryPackage = import ./query-package.nix base;

      overlays.default = final: prev: ports;

      packages.${system} =
      {
        # Test Fil-C cross-compilation
        test-cross-hello =
          let
            nixpkgs-with-filc = import nixpkgs-filc {
              localSystem = { inherit system; };
              crossSystem = {
                config = "x86_64-unknown-linux-filc";
              };
              config.replaceCrossStdenv =
                {
                  buildPackages,
                  baseStdenv,
                }:
                toolchain.filenv;
            };
          in
          nixpkgs-with-filc.lynx;

        # Main compiler and toolchain
        inherit filc;
        inherit (toolchain) filcc filenv;

        # Ports
        inherit ports;
        inherit (ports) port;

        # Shells
        filc-world-shell = shell-world;

        # Virtualization
        filc-nspawn = virt-nspawn;
        filc-qemu = virt-qemu;
        filc-docker = virt-docker;

        # Demos
        lighttpd-demo = base.callPackage ./httpd { inherit ports; };

        # Utilities
        push-filcc = base.writeShellScriptBin "push-filcc" ''
          cachix push filc ${toolchain.filcc}
        '';

        push-pkg = base.writeShellScriptBin "push-pkg" ''
          for pkg in "$@"; do
            cachix push filc $(nix build .#"$pkg" --print-out-paths --no-link)
          done
        '';
      }
      // ports # Export all ported packages at top level
      ;

      apps.${system} = {
        run-filc-docker = {
          type = "app";
          program = "${virt-docker}";
        };

        run-filc-sandbox = {
          type = "app";
          program = "${base.writeShellScript "filc-sandbox" ''
            exec sudo systemd-nspawn --ephemeral \
              -M filbox \
              -D ${virt-nspawn} /bin/runit-init
          ''}";
        };

        run-filc-qemu = {
          type = "app";
          program = "${virt-qemu}/bin/run-filc-qemu";
        };

        build-filc-qemu-image = {
          type = "app";
          program = "${virt-qemu}/bin/build-filc-qemu-image";
        };

        debug-filc-qemu = {
          type = "app";
          program = "${virt-qemu}/bin/debug-filc-qemu";
        };
      };

      formatter.${system} = base.nixfmt-rfc-style;

      devShells.${system} = {
        default = shell-world;
        world = shell-world;
        wasm3-cve = shell-wasm3-cve;
        world-pkgs = shell-world.world-pkgs;
      };
    };
}
