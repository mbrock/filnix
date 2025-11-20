{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    # Modified nixpkgs with Fil-C cross-compilation support
    nixpkgs.url = "github:lessrest/filnixpkgs/400439b089773d3fc593b512250e283a33485de4";
    nixpkgs.flake = false;
  };

  outputs =
    {
      self,
      nixpkgs,
      ...
    }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };

      filcc = import ./toolchain.nix { inherit pkgs; };
      runfilc = import ./tools/runfilc.nix { inherit pkgs filcc; };

      pkgsFilc = import nixpkgs {
        localSystem = system;
        crossSystem.config = "x86_64-unknown-linux-gnufilc0";
        config.replaceCrossStdenv =
          { buildPackages, baseStdenv }:
          baseStdenv.override {
            cc = filcc;
          };
        crossOverlays = [
          (final: prev: {
            gnufilc0 = filcc;
          })
          (import ./ports/overlay.nix pkgs)
        ];
      };

      filc-shell-stuff = import ./shells/world.nix {
        inherit
          pkgs
          filcc
          runfilc
          ;
        ports = pkgsFilc;
      };

      # shell-wasm3-cve = import ./shells/wasm3-cve-test.nix {
      #   inherit pkgs;
      #   ports = pkgsFilcWithOverlay;
      # };

      filc-world-shell = filc-shell-stuff.filc-world-shell;

      virt = import ./virt.nix {
        inherit pkgs filcc;
        ports = pkgsFilc;
        inherit (filc-shell-stuff) world-pkgs;
      };

      uacme-tools = import ./tools/uacme.nix {
        pkgs = pkgsFilc;
      };

      emacs-safe = import ./emacs/emacs.nix {
        inherit pkgs pkgsFilc;
      };

      emacs-unsafe = import ./emacs/emacs.nix {
        inherit pkgs;
        pkgsFilc = pkgs;
      };

      demo = import ./demo.nix {
        inherit pkgs pkgsFilc filcc;
        filc-emacs = emacs-safe.filc-emacs;
      };
    in
    {
      lib.${system}.queryPackage = import ./scripts/query-package.nix pkgs;

      overlays.default = import ./ports/overlay.nix pkgs;

      # Export the full cross-compiled package sets
      legacyPackages.${system} = {
        inherit pkgsFilc;
      };

      packages.${system} = {
        inherit filcc;

        inherit filc-world-shell;
        inherit (virt) filc-nspawn filc-qemu filc-docker;
        inherit (demo)
          lighttpd-demo
          ttyd-emacs-demo
          lua-with-stuff
          python-with-stuff
          python-web-demo
          perl-demos
          perl-with-stuff
          ;

        push-filcc = pkgs.writeShellScriptBin "push-filcc" ''
          cachix push filc ${filcc}
        '';

        push-pkg = pkgs.writeShellScriptBin "push-pkg" ''
          for pkg in "$@"; do
            cachix push filc $(nix build .#"$pkg" --print-out-paths --no-link)
          done
        '';

        inherit runfilc;

        inherit (emacs-safe) filc-emacs;
        emacs = emacs-safe.filc-emacs;
        emacs-unsafe = emacs-unsafe.filc-emacs;

        # ACME/Let's Encrypt tools
        inherit (uacme-tools) uacme challengeServer getFilcCert;
      };

      apps.${system} = virt.apps // {
        runfilc = {
          type = "app";
          program = "${self.packages.${system}.runfilc}/bin/runfilc";
        };

        demo = {
          type = "app";
          program = "${demo.python-web-demo}/bin/filc-demo";
        };

        ttyd-emacs = {
          type = "app";
          program = "${demo.ttyd-emacs-demo}/bin/ttyd-emacs-demo";
        };

        get-cert = {
          type = "app";
          program = "${self.packages.${system}.getFilcCert}/bin/uacme-get-cert";
        };

        perl-demos = {
          type = "app";
          program = "${demo.perl-demos}/bin/perl-demo";
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
