{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    # Modified nixpkgs with Fil-C cross-compilation support
    # filc-aarch64: 118d872 plus aarch64 in the gnufilc0 ABI assertion.
    nixpkgs.url = "github:lessrest/filnixpkgs/e63c68034d742160a48ca80640442337e6356cf4";
    nixpkgs.flake = false;
  };

  outputs =
    {
      self,
      nixpkgs,
      ...
    }:
    let
      nixlib = import "${nixpkgs}/lib";
      # The system-independent outputs (overlays, NixOS modules and machines)
      # come from x86_64-linux; everything keyed by system comes from both.
      perSystem =
        system:
        let
          pkgs = import nixpkgs { inherit system; };

          filcc = import ./toolchain.nix { inherit pkgs; };
          sarcasm = import ./packages/sarcasm.nix { inherit pkgs; };
          sarcasm-prolog = import ./packages/sarcasm-prolog.nix {
            inherit pkgs filcc;
            trealla = pkgsFilc.trealla;
          };
          zstd-sarcasm = import ./ports/zstd-sarcasm.nix {
            inherit pkgs;
            zstd = pkgsFilc.zstd;
          };
          projeny = pkgs.callPackage ./packages/projeny.nix { };
          runfilc = import ./tools/runfilc.nix { inherit pkgs filcc; };

          # The Fil-C package set. blockRustGo marks Rust and Go packages
          # broken (lib/block-rust-go.nix); crossOverlays apply after the ports.
          mkPkgsFilc =
            {
              blockRustGo ? false,
              crossOverlays ? [ ],
            }:
            import nixpkgs {
              localSystem = system;
              crossSystem.config = "${pkgs.stdenv.hostPlatform.parsed.cpu.name}-unknown-linux-gnufilc0";
              config.replaceCrossStdenv =
                { buildPackages, baseStdenv }:
                let
                  stdenv = baseStdenv.override {
                    cc = filcc;
                  };
                in
                if blockRustGo then
                  import ./lib/block-rust-go.nix {
                    inherit (buildPackages) lib stdenvAdapters;
                  } stdenv
                else
                  stdenv;
              crossOverlays = [
                (final: prev: {
                  gnufilc0 = filcc;
                })
                (import ./ports/overlay.nix pkgs)
              ]
              ++ crossOverlays;

              overlays = [
                (import ./ports/build-tools.nix)
              ];
            };

          pkgsFilc = mkPkgsFilc { };

          filc-shell-stuff = import ./shells/world.nix {
            inherit
              pkgs
              filcc
              runfilc
              ;
            ports = pkgsFilc;
          };

          filc-world-shell = filc-shell-stuff.filc-world-shell;
          baseline = import ./shells/baseline.nix {
            inherit
              pkgs
              filcc
              sarcasm
              projeny
              ;
            ports = pkgsFilc;
          };

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

          makeLibei =
            erlang: pkgsFilc.callPackage ./packages/libei.nix { inherit erlang; };
          libei = makeLibei pkgs.erlang;
          libei_27 = makeLibei pkgs.erlang_27;
          libei_28 = makeLibei pkgs.erlang_28;

          demo = import ./demo.nix {
            inherit
              pkgs
              pkgsFilc
              filcc
              libei
              ;
            filc-emacs = emacs-safe.filc-emacs;
          };

          # Ruby with individual gems for testing - auto-generated for all available gems
          rubyWithGem = pkgs.lib.mapAttrs (
            name: _: pkgsFilc.ruby.withPackages (ps: [ ps.${name} ])
          ) pkgsFilc.rubyPackages;
        in
        {
          lib.${system} = {
            queryPackage = import ./scripts/query-package.nix pkgs;
            inherit mkPkgsFilc;
          };

          checks.${system} = {
            pipewire =
              (import ./tests/pipewire.nix { inherit pkgs pkgsFilc filcc; }).pipewire;
            pipewire-runtime =
              (import ./tests/pipewire.nix { inherit pkgs pkgsFilc filcc; }).runtime;
            cancellation = import ./tests/cancellation.nix { inherit pkgs filcc; };
            cancellation-native = import ./tests/cancellation-native.nix {
              inherit pkgs;
            };
            sarcasm-prolog = import ./tests/sarcasm-prolog.nix {
              inherit pkgs filcc sarcasm-prolog;
              trealla = pkgsFilc.trealla;
            };
            trealla = import ./tests/trealla.nix {
              inherit pkgs filcc;
              trealla = pkgsFilc.trealla;
            };
            zstd-sarcasm = import ./tests/zstd-sarcasm.nix {
              inherit pkgs filcc;
              zstd = zstd-sarcasm;
            };
            baseline = baseline.baseline;
            openssl-sarcasm = import ./tests/openssl-sarcasm.nix {
              inherit pkgs filcc;
              openssl = pkgsFilc.openssl-sarcasm;
            };
            sarcasm = import ./tests/sarcasm.nix { inherit pkgs filcc; };
            libtool-symbols = import ./tests/libtool-symbols.nix {
              inherit pkgs filcc;
            };
            inherit projeny;
            libffi = import ./tests/libffi.nix {
              inherit pkgs filcc;
              inherit (pkgsFilc) libffi;
            };
            gtk2-runtime = import ./tests/gtk2-runtime.nix {
              inherit pkgs pkgsFilc;
            };
            gtk3-runtime = import ./tests/gtk-runtime.nix {
              inherit pkgs pkgsFilc;
              major = 3;
            };
            gnutls-tls = import ./tests/gnutls-tls.nix {
              inherit pkgs pkgsFilc;
            };
            utf8-locale = import ./tests/locale.nix { inherit pkgsFilc; };
            pthread-pi = import ./tests/pthread-pi.nix { inherit pkgsFilc; };
            pthread-spin = import ./tests/pthread-spin.nix { inherit pkgsFilc; };
            fenv = import ./tests/fenv.nix { inherit pkgsFilc; };
            wrapper-roles = import ./tests/wrapper-roles.nix { inherit pkgsFilc; };
            gc-local-arrays = import ./tests/gc-local-arrays.nix { inherit pkgsFilc; };
            nix-eval = import ./tests/nix-eval.nix { inherit pkgsFilc; };
            nixos-filc = import ./tests/nixos-filc.nix {
              inherit pkgs;
              filcModule = self.nixosModules.filc;
            };
            perl-xs-pointers = import ./tests/perl-xs-pointers.nix { inherit pkgsFilc; };
            python-decimal = import ./tests/python-decimal.nix { inherit pkgsFilc; };
            python-protobuf = import ./tests/python-protobuf.nix {
              inherit pkgs pkgsFilc;
            };
            cxx-coroutines = import ./tests/cxx-coroutines.nix { inherit pkgsFilc; };
            pointer-tagging = import ./tests/pointer-tagging.nix { inherit pkgsFilc; };
            link-hygiene = import ./tests/link-hygiene.nix { inherit pkgsFilc; };
            fork-regressions = import ./tests/fork-regressions.nix { inherit pkgsFilc; };
            icu = import ./tests/icu.nix {
              inherit pkgs pkgsFilc;
            };
            boost-context = import ./tests/boost-context.nix { inherit pkgsFilc; };
            qnode = import ./tests/qnode.nix { inherit pkgs pkgsFilc; };
            protobuf = import ./tests/protobuf.nix { inherit pkgs pkgsFilc; };
            protobuf_33 = import ./tests/protobuf.nix {
              inherit pkgs pkgsFilc;
              protobuf = pkgsFilc.protobuf_33;
            };
            protobuf_21 = import ./tests/protobuf.nix {
              inherit pkgs pkgsFilc;
              protobuf = pkgsFilc.protobuf_21;
            };
            re2 = import ./tests/re2.nix { inherit pkgs pkgsFilc; };
            emacs-treesit = import ./tests/emacs-treesit.nix {
              inherit pkgs pkgsFilc;
            };
            libsoup3-runtime = import ./tests/libsoup.nix {
              inherit pkgs pkgsFilc;
            };
            gi-link-environment = import ./tests/gi-link-environment.nix {
              inherit pkgs pkgsFilc;
            };
            generator-precedence = import ./tests/generator-precedence.nix {
              inherit pkgs pkgsFilc;
            };
            media-foundations = import ./tests/media-foundations.nix {
              inherit pkgs pkgsFilc;
            };
            glib-atomic = import ./tests/glib-atomic.nix { inherit pkgs pkgsFilc; };
            glib-gtype = import ./tests/glib-gtype.nix { inherit pkgs pkgsFilc; };
            glib-enums = import ./tests/glib-enums.nix { inherit pkgs pkgsFilc; };
            dbus-glib = import ./tests/dbus-glib.nix { inherit pkgs pkgsFilc; };
            glibmm = (import ./tests/glibmm.nix { inherit pkgs pkgsFilc; }).glibmm;
            glibmm_2_68 =
              (import ./tests/glibmm.nix { inherit pkgs pkgsFilc; }).glibmm_2_68;
            gtkmm3-runtime = import ./tests/gtkmm.nix {
              inherit pkgs pkgsFilc;
              major = 3;
            };
            gtkmm4-runtime = import ./tests/gtkmm.nix {
              inherit pkgs pkgsFilc;
              major = 4;
            };
            glib-networking = import ./tests/glib-networking.nix {
              inherit pkgs pkgsFilc;
            };
            pygobject = import ./tests/pygobject.nix {
              inherit pkgs pkgsFilc;
            };
            gtk4-runtime = import ./tests/gtk-runtime.nix {
              inherit pkgs pkgsFilc;
              major = 4;
            };
          };

          overlays.default = import ./ports/overlay.nix pkgs;

          # Run chosen NixOS services and programs as Fil-C builds; see
          # nixos/filc.nix, docs/nixos.md and the two example machines.
          nixosModules = rec {
            filc = import ./nixos/filc.nix { filnix = self; };
            default = filc;
          };
          # A finix system whose whole userland is Fil-C; see finix/userland.nix.
          finixModules = rec {
            filc-userland = import ./finix/userland.nix { filnix = self; };
            default = filc-userland;
          };

          nixosConfigurations =
            let
              machine =
                module:
                import "${nixpkgs}/nixos/lib/eval-config.nix" {
                  inherit system;
                  modules = [
                    self.nixosModules.filc
                    module
                  ];
                };
            in
            {
              filc-demo = machine ./nixos/demo.nix;
              ec2-filc = machine ./nixos/ec2.nix;
            };

          # Export the full cross-compiled package sets
          legacyPackages.${system} = {
            inherit pkgsFilc;
          };

          packages.${system} = {
            baseline = baseline.baseline;
            baseline-shell = baseline.shell;
            inherit
              filcc
              projeny
              sarcasm
              sarcasm-prolog
              zstd-sarcasm
              ;
            inherit (sarcasm) minilute;
            inherit (pkgsFilc) openssl-sarcasm;
            inherit
              libei
              libei_27
              libei_28
              ;

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
              libei-ping-demo
              sinatra-demo
              ;

            push-baseline = pkgs.writeShellApplication {
              name = "filc-push-baseline";
              runtimeInputs = [
                pkgs.nix
                pkgs.cachix
                pkgs.coreutils
                (pkgs.writeScriptBin "filc-verify-cache" (
                  "#!${pkgs.python3}/bin/python3\n"
                  + builtins.readFile ./scripts/verify-cache.py
                ))
              ];
              text = builtins.readFile ./scripts/push-baseline.sh;
            };

            push-filcc = pkgs.writeShellScriptBin "push-filcc" ''
              ${pkgs.cachix}/bin/cachix push filc ${filcc}
            '';

            push-pkg = pkgs.writeShellScriptBin "push-pkg" ''
              for pkg in "$@"; do
                ${pkgs.cachix}/bin/cachix push filc $(${pkgs.nix}/bin/nix build .#"$pkg" --print-out-paths --no-link)
              done
            '';

            inherit runfilc;

            inherit rubyWithGem;

            inherit (emacs-safe) filc-emacs;
            emacs30 = pkgsFilc.emacs30;
            emacs = emacs-safe.filc-emacs;
            emacs-unsafe = emacs-unsafe.filc-emacs;
          };

          apps.${system} = virt.apps // {
            zstd-sarcasm = {
              type = "app";
              program = "${zstd-sarcasm.bin}/bin/zstd";
            };
            baseline = {
              type = "app";
              program = "${baseline.shell}/bin/filc-baseline-shell";
            };
            openssl-sarcasm = {
              type = "app";
              program = "${pkgsFilc.openssl-sarcasm.bin}/bin/openssl";
            };
            filcc = {
              type = "app";
              program = "${filcc}/bin/clang";
            };

            "filc++" = {
              type = "app";
              program = "${filcc}/bin/clang++";
            };
          };

          formatter.${system} = pkgs.nixfmt;

          devShells.${system} = {
            default = pkgs.mkShell {
              name = "filnix-dev";
              packages = with pkgs; [
                # Nix development tools
                nixfmt
                treefmt
                nixd
                nil

                projeny
                python3

                # General development tools
                git
                direnv
                nix-direnv
              ];

              shellHook = ''
                git config core.hooksPath scripts/git-hooks
              '';
            };

            # Full Fil-C compilation environment (opt-in with 'nix develop .#world')
            world = filc-world-shell;

            # Incremental Fil-C LLVM hacking; see docs/llvm-dev.md
            filc-llvm = import ./shells/filc-llvm.nix { inherit pkgs; };
          };
        };
    in
    nixlib.recursiveUpdate (builtins.removeAttrs (perSystem "aarch64-linux") [
      "overlays"
      "nixosModules"
      "nixosConfigurations"
      "finixModules"
    ]) (perSystem "x86_64-linux");
}
