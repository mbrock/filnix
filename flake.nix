{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/c8aa8cc00a5cb57fada0851a038d35c08a36a2bb";
    # Modified nixpkgs with Fil-C cross-compilation support
    nixpkgs-filc.url = "github:lessrest/filnixpkgs/400439b089773d3fc593b512250e283a33485de4";
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

      pkgsFilc = import nixpkgs-filc {
        localSystem = system;
        crossSystem.config = "x86_64-unknown-linux-gnufilc0";
        config.replaceCrossStdenv =
          { buildPackages, baseStdenv }:
          baseStdenv.override {
            cc = toolchain.filcc;
          };
        crossOverlays = [
          (final: prev: {
            gnufilc0 = toolchain.filcc;
          })
          (import ./ports/overlay.nix pkgs)
        ];
      };

      pkgsFilc2 = import nixpkgs-filc {
        localSystem = system;
        crossSystem.config = "x86_64-unknown-linux-gnufilc0";
        config.replaceCrossStdenv =
          { buildPackages, baseStdenv }:
          baseStdenv.override {
            cc = toolchain.filcc;
          };
        crossOverlays = [
          (final: prev: {
            gnufilc0 = toolchain.filcc;
          })
          (import ./ports/overlay.nix pkgs)
        ];
      };

      filc-shell-stuff = import ./shells/world.nix {
        inherit
          pkgs
          toolchain
          runfilc
          ;
        ports = pkgsFilc;
      };

      # shell-wasm3-cve = import ./shells/wasm3-cve-test.nix {
      #   inherit pkgs;
      #   ports = pkgsFilcWithOverlay;
      # };

      filc-world-shell = filc-shell-stuff.filc-world-shell;

      filc-nspawn = import ./virt/nspawn.nix {
        inherit pkgs;
        ports = pkgsFilc;
        filcc = toolchain.filcc;
        inherit (filc-shell-stuff) world-pkgs;
      };

      filc-qemu = import ./virt/qemu.nix {
        inherit pkgs;
        ports = pkgsFilc;
        filcc = toolchain.filcc;
        inherit (filc-shell-stuff) world-pkgs;
      };

      filc-docker = import ./virt/docker.nix {
        inherit pkgs;
        ports = pkgsFilc;
        filcc = toolchain.filcc;
        inherit (filc-shell-stuff) world-pkgs;
      };

      runfilc = import ./tools/runfilc.nix { inherit pkgs toolchain; };

      emacs-safe = import ./emacs/emacs.nix {
        inherit pkgs;
        pkgsFilc = pkgsFilc2;
      };

      emacs-unsafe = import ./emacs/emacs.nix {
        inherit pkgs;
        pkgsFilc = pkgs;
      };
    in
    {
      lib.${system}.queryPackage = import ./scripts/query-package.nix pkgs;

      overlays.default = import ./ports/overlay.nix pkgs;

      # Export the full cross-compiled package sets
      legacyPackages.${system} = {
        inherit pkgsFilc pkgsFilc2;
      };

      packages.${system} = {
        inherit filc0;
        filcc = toolchain.filcc;
        filc-bintools = toolchain.filc-bintools;

        inherit filc-world-shell;
        inherit filc-nspawn;
        inherit filc-qemu;
        inherit filc-docker;

        lighttpd-demo = pkgs.callPackage ./httpd {
          ports = pkgsFilc;
          filcc = toolchain.filcc;
        };

        ttyd-emacs-demo = pkgs.callPackage ./ttyd-demo {
          ports = pkgsFilc;
          filc-emacs = emacs-safe.filc-emacs;
        };

        push-filcc = pkgs.writeShellScriptBin "push-filcc" ''
          cachix push filc ${toolchain.filcc}
        '';

        push-pkg = pkgs.writeShellScriptBin "push-pkg" ''
          for pkg in "$@"; do
            cachix push filc $(nix build .#"$pkg" --print-out-paths --no-link)
          done
        '';

        inherit runfilc;

        lua-with-stuff = pkgsFilc.lua5.withPackages (
          ps: with ps; [
            lpeg
            luafilesystem
            luabitop
            luadbi
            luadbi-sqlite3
            luaffi
            lua-ffi-zlib
            luaposix
            lua-pam
          ]
        );

        python-with-stuff = pkgsFilc.python3.withPackages (
          ps: with ps; [
            (lxml.overrideAttrs (_: {
              env.CFLAGS = "-O0";
            }))
            uvicorn
            starlette
            msgspec
            tagflow
            pycairo
            rich
            python-multipart
          ]
        );

        python-web-demo = pkgsFilc.callPackage ./demo {
          demo-src = ./demo;
        };

        perl-demos = pkgsFilc.callPackage ./demo/perl { };

        perl-with-stuff = pkgsFilc.perl.withPackages (
          ps: with ps; [
            InlineC
            # JSONXS
            # YAMLLibYAML
            # DBI
            # DBDSQLite
            #            ack
          ]
        );

        inherit (emacs-safe) filc-emacs;
        emacs = emacs-safe.filc-emacs;
        emacs-unsafe = emacs-unsafe.filc-emacs;
      };

      apps.${system} = {
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

        runfilc = {
          type = "app";
          program = "${self.packages.${system}.runfilc}/bin/runfilc";
        };

        demo = {
          type = "app";
          program = "${self.packages.${system}.python-web-demo}/bin/filc-demo";
        };

        ttyd-emacs = {
          type = "app";
          program = "${self.packages.${system}.ttyd-emacs-demo}/bin/ttyd-emacs-demo";
        };

        perl-demos = {
          type = "app";
          program = "${self.packages.${system}.perl-demos}/bin/perl-demo";
        };

      };

      formatter.${system} = pkgs.nixfmt-rfc-style;

      devShells.${system} = {
        default = pkgs.mkShell {
          name = "filnix-dev";
          packages = with pkgs; [
            # Nix development tools
            nixfmt-rfc-style
            nixd
            nil

            # General development tools
            git
            direnv
            nix-direnv
          ];

          shellHook = ''
            # Get git info
            branch=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "no-git")
            if git diff-index --quiet HEAD -- 2>/dev/null; then
              status="✓"
            else
              status="●"
            fi

            echo
            # All three lines of logo in bold
            tput bold 2>/dev/null || true
            printf "  ┌─┐┬┬  ┌─┐    "
            tput sgr0 2>/dev/null || true; tput dim 2>/dev/null || true
            printf "⎇ %s %s\n" "$branch" "$status"
            tput sgr0 2>/dev/null || true; tput bold 2>/dev/null || true
            printf "  ├┤ ││──│  \n"
            printf "  └  ┴┴─┘└─┘\n"
            tput sgr0 2>/dev/null || true
            echo
            # Recent commits
            git log -3 --pretty=format:'  %C(cyan)%h%C(reset) %s %C(dim)%ar%C(reset)' 2>/dev/null
            tput sgr0 2>/dev/null || true
            echo; echo
          '';
        };

        # Full Fil-C compilation environment (opt-in with 'nix develop .#world')
        world = filc-world-shell;

        # Perl demos development environment
        perl-demos = pkgs.mkShell {
          name = "filc-perl-demos";
          packages = [
            (pkgsFilc.perl.withPackages (
              ps: with ps; [
                # C integration
                InlineC

                # Fast C-based data processing
                JSONXS
                YAMLLibYAML # YAML::LibYAML - fast C-based YAML parser

                # Database with C backend
                DBI
                DBDSQLite

                # XML parsing (libxml2)
                XMLLibXML

                # Compression (zlib, bzip2)
                CompressZlib
                CompressBzip2

                # Other useful XS modules
                ListMoreUtils
                ScalarListUtils
              ]
            ))
          ];

          shellHook = ''
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo "  Perl + C Integration with Fil-C Memory Safety"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo
            echo "Demo scripts:"
            echo "  perl demo.pl      - Multiple C libraries (JSON, XML, SQLite, zlib)"
            echo "  perl inline-c.pl  - Write memory-safe C directly in Perl"
            echo "  ./run-all.sh      - Run both demos"
            echo
            echo "✓ All C code compiled with Fil-C memory safety"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo
          '';
        };
      };
    };
}
