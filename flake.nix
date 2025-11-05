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
      pkgs = import nixpkgs { inherit system; };

      sources = import ./lib/sources.nix { inherit pkgs; };

      filc0 = (import ./compiler/filc0.nix { inherit pkgs; }).filc0;
      filc = import ./build-filc.nix { inherit pkgs filc0; };
      filc-binutils = import ./toolchain/binutils.nix { inherit pkgs; };
      filc-sysroot = import ./toolchain/sysroot.nix { inherit pkgs filc; };
      toolchain = import ./toolchain/wrappers.nix {
        inherit
          pkgs
          filc
          filc-sysroot
          filc-binutils
          ;
      };

      ports = import ./ports.nix {
        inherit pkgs;
        inherit (toolchain)
          filenv
          withFilC
          fix
          filcc
          ;
        filc-src = sources.filc0-src;
      };

      filc-shell-stuff = import ./shells/world.nix {
        inherit pkgs toolchain ports;
      };

      shell-wasm3-cve = import ./shells/wasm3-cve-test.nix {
        inherit pkgs ports;
      };

      filc-shell = filc-shell-stuff.filc-world-shell;

      filc-nspawn = import ./virt/nspawn.nix {
        inherit pkgs ports;
        inherit (filc-shell-stuff) world-pkgs;
      };

      filc-qemu = import ./virt/qemu.nix {
        inherit pkgs ports;
        inherit (filc-shell-stuff) world-pkgs;
      };

      filc-docker = import ./virt/docker.nix {
        inherit pkgs ports;
        inherit (filc-shell-stuff) world-pkgs;
      };

      pkgsFilc = import nixpkgs-filc {
        localSystem = { inherit system; };
        crossSystem.config = "x86_64-unknown-linux-filc";
        config.replaceCrossStdenv = _: toolchain.filenv;
      };
    in
    {
      lib.${system}.queryPackage = import ./query-package.nix pkgs;

      overlays.default = final: prev: ports;

      packages.${system} = {
        test-cross-hello = pkgsFilc.lynx;

        inherit filc0;
        filcc = toolchain.filcc;

        inherit filc-shell;
        inherit filc-nspawn;
        inherit filc-qemu;
        inherit filc-docker;

        lighttpd-demo = pkgs.callPackage ./httpd { inherit ports; };

        push-filcc = pkgs.writeShellScriptBin "push-filcc" ''
          cachix push filc ${toolchain.filcc}
        '';

        push-pkg = pkgs.writeShellScriptBin "push-pkg" ''
          for pkg in "$@"; do
            cachix push filc $(nix build .#"$pkg" --print-out-paths --no-link)
          done
        '';
      }
      // ports;

      apps.${system} = {
        run-filc-docker = {
          type = "app";
          program = filc-docker;
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

      formatter.${system} = pkgs.nixfmt-rfc-style;

      devShells.${system} = {
        default = filc-shell-stuff;
        wasm3-cve = shell-wasm3-cve;
      };
    };
}
