{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/c8aa8cc00a5cb57fada0851a038d35c08a36a2bb";
  };

  outputs =
    { self, nixpkgs, ... }:
    let
      system = "x86_64-linux";
      base = import nixpkgs { inherit system; };

      # Import helper libraries and sources
      lib = import ./lib { inherit base; };
      sources = import ./lib/sources.nix { inherit base; };

      # Build runtime and compiler using a fixed-point to resolve circular dependencies
      # The runtime needs the compiler, and the compiler needs the runtime
      fix =
        let
          # Stage 1: Build runtime without compiler dependencies
          runtime-stage1 = import ./runtime {
            inherit base lib sources;
            filc1-runtime = null;
            filc2 = null;
          };

          # Stage 2: Build compiler stage 1 with libyolo
          compiler-stage1 = import ./compiler/filc0.nix { inherit base lib sources; };
          compiler-stage1b = import ./compiler/filc1.nix {
            inherit base lib;
            inherit (compiler-stage1) filc0;
            inherit (runtime-stage1) libyolo-glibc libyolo filc-stdfil-headers;
          };

          # Stage 3: Build libpizlo with filc1-runtime
          runtime-stage2 = import ./runtime {
            inherit base lib sources;
            filc1-runtime = compiler-stage1b.filc1-runtime;
            filc2 = null;
          };

          # Stage 4: Build compiler stage 2 with libpizlo
          compiler-stage2 = import ./compiler/filc2.nix {
            inherit base lib;
            inherit (compiler-stage1) filc0;
            inherit (runtime-stage2)
              libyolo
              libyolo-glibc
              libpizlo
              filc-stdfil-headers
              ;
          };

          # Stage 5: Build libmojo with filc2
          runtime-stage3 = import ./runtime {
            inherit base lib sources;
            inherit (compiler-stage1b) filc1-runtime;
            filc2 = compiler-stage2.filc2;
          };

          # Stage 6: Build complete compiler with all stages
          compiler-final = import ./compiler {
            inherit base lib sources;
            runtime = runtime-stage3;
          };

        in
        {
          runtime = runtime-stage3;
          compiler = compiler-final;
        };

      inherit (fix) runtime compiler;

      # Build toolchain (binutils, sysroot, wrappers)
      toolchain = import ./toolchain {
        inherit
          base
          lib
          runtime
          compiler
          ;
      };

      # Port set for ported packages
      portset = import ./portset.nix {
        inherit base;
        inherit (toolchain)
          filenv
          withFilC
          fix
          filcc
          ;
        filc-src = sources.filc0-src;
      };

      # Additional utilities
      ghostty-terminfo = base.runCommand "ghostty-terminfo" { } ''
        mkdir -p $out/share/terminfo
        ${base.ncurses}/bin/tic -x -o $out/share/terminfo ${./ghostty.terminfo}
      '';

      dank-bashrc = base.writeText "dank-bashrc" ''
        echo
        tput bold
        figlet -f fender "Fil-C" | sed 's/^/   /' | clolcat -f | head -n-1
        tput sgr0; tput dim
        echo -n '    '; clang 2>&1 -v | grep Fil-C
        tput sgr0
        echo; echo '  You feel an uncanny sense of safety...'
        tput sgr0
        echo

        export CC=filc
        export CXX=filc++
        export PKG_CONFIG=pkgconf
      '';

      # CVE test payloads for wasm3
      wasm3-cve-payloads = (import ./wasm3-cves.nix { pkgs = base; }).cve-tests;

      # Build shells
      shells = import ./shells {
        inherit
          base
          toolchain
          compiler
          runtime
          portset
          wasm3-cve-payloads
          ghostty-terminfo
          dank-bashrc
          ;
      };

      # Virtualization variants (nspawn, qemu, docker)
      virt = import ./virt {
        inherit
          base
          ghostty-terminfo
          dank-bashrc
          ;
        ports = portset;
        world-pkgs = shells.world-pkgs;
      };

      world-pkgs = shells.world-pkgs;

      # Legacy docker image (non-runit)
      filc-world-docker = import ./filc-world-docker.nix {
        inherit
          base
          ghostty-terminfo
          dank-bashrc
          ;
        ports = portset;
        world-pkgs = shells.world-pkgs;
      };

    in
    {
      lib.${system}.queryPackage = import ./query-package.nix base;

      packages.${system} =
      {
        # Compiler stages
        inherit (compiler)
          filc0
          filc1
          filc2
          filc-libcxx
          ;

        # Runtime libraries
        inherit (runtime)
          libyolo-glibc
          libyolo
          libpizlo
          libmojo
          ;

        # Toolchain
        inherit (toolchain) filc-sysroot filc-binutils filcc;

        # Portset
        inherit portset;
        inherit (portset) port;

        # Shells
        inherit (shells) filc-world-shell;

        # Virtualization
        inherit virt;
        filc-nspawn = virt.nspawn;
        filc-qemu = virt.qemu;
        filc-docker = virt.docker;

        # Legacy
        inherit filc-world-docker;

        # Demos
        lighttpd-demo = base.callPackage ./httpd { portset = portset; };

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
      // portset # Export all ported packages at top level
      ;

      apps.${system} = {
        run-filc-world-docker = {
          type = "app";
          program = "${filc-world-docker}";
        };

        run-filc-docker = {
          type = "app";
          program = "${virt.docker}";
        };

        run-filc-sandbox = {
          type = "app";
          program = "${base.writeShellScript "filc-sandbox" ''
            exec sudo systemd-nspawn --ephemeral \
              -M filbox \
              -D ${virt.nspawn} /bin/runit-init
          ''}";
        };

        run-filc-qemu = {
          type = "app";
          program = "${virt.qemu}/bin/run-filc-qemu";
        };

        build-filc-qemu-image = {
          type = "app";
          program = "${virt.qemu}/bin/build-filc-qemu-image";
        };

        debug-filc-qemu = {
          type = "app";
          program = "${virt.qemu}/bin/debug-filc-qemu";
        };
      };

      formatter.${system} = base.nixfmt-rfc-style;

      devShells.${system} = shells;
    };
}
