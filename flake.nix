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

        overlays = [
          # (final: prev: {
          #   inherit (import ./ports/overlay.nix pkgs final prev) glib gobject-introspection-unwrapped;
          # })
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

      filc-world-shell = filc-shell-stuff.filc-world-shell;

      virt = import ./virt.nix {
        inherit pkgs filcc;
        ports = pkgsFilc;
        inherit (filc-shell-stuff) world-pkgs;
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

      # Ruby with individual gems for testing - auto-generated for all available gems
      rubyWithGem = pkgs.lib.mapAttrs
        (name: _: pkgsFilc.ruby.withPackages (ps: [ ps.${name} ]))
        pkgsFilc.rubyPackages;
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
          ruby-maxxed
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

        inherit rubyWithGem;

        inherit (emacs-safe) filc-emacs;
        emacs = emacs-safe.filc-emacs;
        emacs-unsafe = emacs-unsafe.filc-emacs;
      };

      apps.${system} = virt.apps // {
        filcc = {
          type = "app";
          program = "${filcc}/bin/clang";
        };

        "filc++" = {
          type = "app";
          program = "${filcc}/bin/clang++";
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
        };

        # Full Fil-C compilation environment (opt-in with 'nix develop .#world')
        world = filc-world-shell;
      };
    };
}
