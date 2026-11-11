{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    # Modified nixpkgs with Fil-C cross-compilation support
    # filc-aarch64: 118d872 plus aarch64 in the gnufilc0 ABI assertion.
    nixpkgs.url = "github:lessrest/filnixpkgs/e63c68034d742160a48ca80640442337e6356cf4";
    nixpkgs.flake = false;
    # For the example finix machine and its test (finix/demo.nix). The last
    # revision before finix required finit 5; filnix's Nixpkgs has finit 4.17.
    finix.url = "github:finix-community/finix/9fafdc3f091e963585a0dd4df028d58c2d66d815";
    finix.flake = false;
  };

  outputs =
    {
      self,
      nixpkgs,
      finix,
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
          stagingSources = import ./lib/sources.nix {
            inherit pkgs;
            variant = "staging";
          };
          filcc-staging = import ./toolchain.nix {
            inherit pkgs;
            sources = stagingSources;
          };
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
              staging ? false,
              blockRustGo ? false,
              crossOverlays ? [ ],
              permittedInsecurePackages ? [ ],
            }:
            let
              cc = if staging then filcc-staging else filcc;
            in
            import nixpkgs {
              localSystem = system;
              crossSystem.config = "${pkgs.stdenv.hostPlatform.parsed.cpu.name}-unknown-linux-gnufilc0";
              config.permittedInsecurePackages = permittedInsecurePackages;
              config.replaceCrossStdenv =
                { buildPackages, baseStdenv }:
                let
                  stdenv = baseStdenv.override {
                    inherit cc;
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
                  gnufilc0 = cc;
                })
                (import ./ports/overlay.nix pkgs)
              ]
              # tzdata's now.ck compares zones from the build date on, so
              # 2026c fails it from 2026-11-01 (Vancouver and Phoenix agree from
              # then). It lints the data, not zic or zdump; run the rest.
              ++ [
                (final: prev: {
                  tzdata = prev.tzdata.overrideAttrs { checkTarget = "check_mild back.ck"; };
                })
              ]
              ++ crossOverlays;

              overlays = [
                (import ./ports/build-tools.nix)
              ];
            };

          pkgsFilc = mkPkgsFilc { };

          # The package set of a whole Fil-C system (lib/filc-system.nix):
          # Rust and Go refused, and the native exceptions taken from a
          # native Nixpkgs, the built-in ones for `os` and those `native`
          # picks from it.
          mkPkgsFilcSystem =
            {
              os,
              native ? _: { },
              nativePackages ? pkgs,
              nativeNix ? true,
            }:
            let
              builtin = nixlib.filterAttrs (
                name: e: nixlib.elem os e.os && (name != "nix" || nativeNix)
              ) (import ./lib/native-exceptions.nix);
            in
            mkPkgsFilc {
              blockRustGo = true;
              crossOverlays = [
                (
                  final: prev:
                  nixlib.mapAttrs (name: _: nativePackages.${name}) builtin
                  // native nativePackages
                )
              ];
            };
          # Shared by every system that adds no exceptions of its own.
          pkgsFilcSystem = nixlib.genAttrs [ "nixos" "finix" ] (
            os: mkPkgsFilcSystem { inherit os; }
          );

          # Explicit reproduction outputs only; the ordinary package set still
          # refuses this vulnerable PHP unless the caller opts in.
          pkgsFilcPhp84_25 = mkPkgsFilc {
            permittedInsecurePackages = [
              "php-8.4.25"
              "php-with-extensions-8.4.25"
            ];
          };
          optfil = import ./packages/optfil {
            inherit
              pkgs
              pkgsFilc
              filcc
              sarcasm
              ;
          };
          # On staging, the PostgreSQL server marks its main segment with
          # zmark_shared and is built with -fzmark-shared (docs/zmark-shared.md).
          # Release systems still refuse it (lib/block-rust-go.nix).
          pkgsFilcStaging = mkPkgsFilc {
            staging = true;
            crossOverlays = [
              (final: prev: {
                postgresql_18 = prev.postgresql_18.overrideAttrs (old: {
                  patches = old.patches ++ [ ./patches/postgresql-filc-zmark-shared.patch ];
                  env = old.env // {
                    CFLAGS = old.env.CFLAGS + " -fzmark-shared";
                  };
                });
              })
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

          nixosImage = import ./nixos/image.nix {
            inherit pkgs;
            inherit (self.nixosConfigurations.base) config;
          };

          # Ruby with individual gems for testing - auto-generated for all available gems
          rubyWithGem = pkgs.lib.mapAttrs (
            name: _: pkgsFilc.ruby.withPackages (ps: [ ps.${name} ])
          ) pkgsFilc.rubyPackages;
        in
        {
          lib.${system} = {
            queryPackage = import ./scripts/query-package.nix pkgs;
            inherit mkPkgsFilc mkPkgsFilcSystem;
            # The native Nixpkgs that a Fil-C system's exceptions come from.
            nativePackages = pkgs;
            # Fil-C docs, pass and runtime at the pin, for reading
            # (lib/sources.nix): nix build .#lib.x86_64-linux.filc-ref-src
            filc-ref-src = (import ./lib/sources.nix { inherit pkgs; }).filc-ref-src;
            filc-staging-ref-src =
              (import ./lib/sources.nix {
                inherit pkgs;
                variant = "staging";
              }).filc-ref-src;
            # checks.nanofil with arguments, such as { shard = "2/6"; } or
            # { withTrealla = true; } (.github/workflows/nanofil.yml).
            nanofil-check =
              args:
              import ./nanofil/nix/check.nix (
                {
                  inherit pkgs;
                  filcc = filcc-staging;
                }
                // args
              );
            # Unsupported ports and known release gaps stay strict and opt-in,
            # outside the ordinary passing contract of flake check.
            diagnostics = {
              pipewire =
                (import ./tests/pipewire.nix { inherit pkgs pkgsFilc filcc; }).pipewire;
              pipewire-runtime =
                (import ./tests/pipewire.nix { inherit pkgs pkgsFilc filcc; }).runtime;
              release-fork-known-gaps = import ./tests/fork-regressions.nix {
                inherit pkgsFilc;
                suite = "release-known-gaps";
              };
            };
          };

          checks.${system} = {
            # Bare ports that land on another attribute than the one written.
            port-names = import ./tests/port-names.nix { inherit pkgs pkgsFilc; };
            port-version-refresh = import ./tests/port-version-refresh.nix {
              inherit pkgs pkgsFilc;
            };
            staging-fork-regressions = import ./tests/fork-regressions.nix {
              pkgsFilc = pkgsFilcStaging;
            };
            staging-llvm-jit = import ./tests/llvm-jit.nix {
              pkgsFilc = pkgsFilcStaging;
            };
            staging-sealed-closures = import ./tests/sealed-closures.nix {
              pkgsFilc = pkgsFilcStaging;
            };
            staging-cxx-coroutines = import ./tests/cxx-coroutines.nix {
              pkgsFilc = pkgsFilcStaging;
            };
            staging-fenv = import ./tests/fenv.nix {
              pkgsFilc = pkgsFilcStaging;
            };
            staging-gc-local-arrays = import ./tests/gc-local-arrays.nix {
              pkgsFilc = pkgsFilcStaging;
            };
            staging-link-hygiene = import ./tests/link-hygiene.nix {
              pkgsFilc = pkgsFilcStaging;
            };
            staging-wrapper-roles = import ./tests/wrapper-roles.nix {
              pkgsFilc = pkgsFilcStaging;
            };
            staging-zmark-shared = import ./tests/zmark-shared.nix {
              inherit pkgs;
              pkgsFilc = pkgsFilcStaging;
            };
            staging-sarcasm = import ./tests/sarcasm.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            staging-sarcasm-fixes = import ./tests/sarcasm-fixes.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            unsafe-call-boundary = import ./tests/unsafe-call-boundary.nix {
              inherit pkgs filcc;
            };
            nanofil = import ./nanofil/nix/check.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-rocq = import ./nanofil/nix/rocq.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-docs = import ./nanofil/nix/docs.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-rocq-parse =
              (import ./nanofil/nix/rocq.nix {
                inherit pkgs;
                filcc = filcc-staging;
              }).parse;
            # The extracted validator on every -O module of the corpus,
            # hello, zlib, Lua and SQLite (.github/workflows/nanofil-gate.yml).
            nanofil-rocq-gate = import ./nanofil/nix/rocq-gate.nix {
              inherit pkgs;
              filcc = filcc-staging;
              driver =
                (import ./nanofil/nix/rocq.nix {
                  inherit pkgs;
                  filcc = filcc-staging;
                }).model.driver;
            };
            nanofil-rocq-full = import ./nanofil/nix/rocq.nix {
              inherit pkgs;
              filcc = filcc-staging;
              full = true;
            };
            nanofil-logic-spikes = import ./nanofil/nix/spikes.nix {
              inherit pkgs;
              filcc = filcc-staging;
              model =
                (import ./nanofil/nix/rocq.nix {
                  inherit pkgs;
                  filcc = filcc-staging;
                }).model;
            };
            # Programs linked with nanofil's IR of user glibc, proved
            # (nanofil/docs/glibc-ir.md); off the main path.
            nanofil-glibc = import ./nanofil/nix/glibc.nix {
              inherit pkgs;
              filcc = filcc-staging;
              model =
                (import ./nanofil/nix/rocq.nix {
                  inherit pkgs;
                  filcc = filcc-staging;
                }).model;
            };
            nanofil-backend = import ./nanofil/nix/backend.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-backend-full = import ./nanofil/nix/backend.nix {
              inherit pkgs;
              filcc = filcc-staging;
              full = true;
            };
            # The same backend extracted to C++ by Crane.
            nanofil-backend-crane = import ./nanofil/nix/backend-crane.nix {
              inherit pkgs;
            };
            nanofil-hello = import ./nanofil/nix/hello.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-hello-glibc = import ./nanofil/nix/hello-glibc.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            # Hello's linked checked module, the Iris proof's fixture.
            nanofil-hello-fixture = import ./nanofil/nix/hello-fixture.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-zlib = import ./nanofil/nix/zlib.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-lua = import ./nanofil/nix/lua.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-bzip2 = import ./nanofil/nix/bzip2.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-lz4 = import ./nanofil/nix/lz4.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-sqlite = import ./nanofil/nix/sqlite.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-sed = import ./nanofil/nix/sed.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-jq = import ./nanofil/nix/jq.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-dash = import ./nanofil/nix/dash.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-xz = import ./nanofil/nix/xz.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-make = import ./nanofil/nix/make.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-coreutils = import ./nanofil/nix/coreutils.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-bash = import ./nanofil/nix/bash.nix {
              inherit pkgs;
              filcc = filcc-staging;
            };
            nanofil-swipl = import ./nanofil/nix/swipl.nix {
              inherit pkgs;
              filcc = filcc-staging;
              pkgsFilc = pkgsFilcStaging;
            };
            inherit
              (import ./nanofil/nix/python.nix {
                inherit pkgs;
                filcc = filcc-staging;
              })
              nanofil-python
              nanofil-python-regrtest-plain
              ;
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
            sarcasm-fixes = import ./tests/sarcasm-fixes.nix {
              inherit pkgs filcc;
            };
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
            # The StealMyBitcoin exploit works end to end on the unstripped
            # Nixpkgs PHP 8.4.25 and is thwarted by pkgsFilc.php84_25, the
            # same vulnerable release under Fil-C (docs/php.md).
            php-stealmybitcoin = import ./tests/php-stealmybitcoin.nix {
              inherit pkgs;
              native =
                (pkgs.php84.overrideAttrs (old: {
                  dontStrip = true;
                  separateDebugInfo = false;
                })).withExtensions
                  (
                    { enabled, ... }:
                    map (
                      ext:
                      if ext.extensionName == "pcntl" then
                        ext.overrideAttrs (old: {
                          # Nix sandboxes may exclude CPU 0. Exercise affinity on
                          # allowed CPUs rather than assuming CPUs 0 and 1 exist.
                          postPatch = (old.postPatch or "") + ''
                            substituteInPlace ext/pcntl/tests/pcntl_cpuaffinity.phpt \
                              --replace-fail '$mask = [0, 1];' \
                                '$mask = array_slice(pcntl_getcpuaffinity(), 0, 2);' \
                              --replace-fail '["0", "1"]' 'array_map("strval", $mask)'
                          '';
                        })
                      else
                        ext
                    ) enabled
                  );
              filc = pkgsFilcPhp84_25.php84_25;
            };
            utf8-locale = import ./tests/locale.nix { inherit pkgsFilc; };
            pthread-pi = import ./tests/pthread-pi.nix { inherit pkgsFilc; };
            pthread-spin = import ./tests/pthread-spin.nix { inherit pkgsFilc; };
            fenv = import ./tests/fenv.nix { inherit pkgsFilc; };
            glibc-dirwalk = import ./tests/glibc-dirwalk.nix { inherit pkgsFilc; };
            glibc-settimezone = import ./tests/glibc-settimezone.nix {
              inherit pkgsFilc;
            };
            glibc-syscall-fallbacks = import ./tests/glibc-syscall-fallbacks.nix {
              inherit pkgsFilc;
            };
            runtime-prctl-caps = import ./tests/runtime-prctl-caps.nix {
              inherit pkgsFilc;
            };
            # Boots the exact nixos-image file and checks its userland.
            nixos-image-boot = nixosImage.check;
            native-exceptions-table = import ./tests/native-exceptions-table.nix {
              inherit pkgs;
            };
            # Boots finixConfigurations.filc-demo; see finix/test.nix.
            finix-filc-demo = import ./finix/test.nix {
              inherit pkgs finix;
              filnix = self;
            };
            wrapper-roles = import ./tests/wrapper-roles.nix { inherit pkgsFilc; };
            gc-local-arrays = import ./tests/gc-local-arrays.nix { inherit pkgsFilc; };
            pch-union = import ./tests/pch-union.nix { inherit pkgsFilc; };
            nix-eval = import ./tests/nix-eval.nix { inherit pkgsFilc; };
            perl-xs-pointers = import ./tests/perl-xs-pointers.nix { inherit pkgsFilc; };
            python-decimal = import ./tests/python-decimal.nix { inherit pkgsFilc; };
            python-protobuf = import ./tests/python-protobuf.nix {
              inherit pkgs pkgsFilc;
            };
            cxx-coroutines = import ./tests/cxx-coroutines.nix { inherit pkgsFilc; };
            pointer-tagging = import ./tests/pointer-tagging.nix { inherit pkgsFilc; };
            link-hygiene = import ./tests/link-hygiene.nix { inherit pkgsFilc; };
            fork-regressions = import ./tests/fork-regressions.nix {
              inherit pkgsFilc;
              suite = "release";
            };
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
            graphite2-runtime = import ./tests/graphite2.nix {
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

          # A NixOS or finix system whose `pkgs` is the Fil-C package set;
          # see lib/filc-system.nix and docs/nixos.md.
          nixosModules.default = import ./nixos { filnix = self; };
          finixModules.default = import ./finix { filnix = self; };
          # A Fil-C NixOS, with the NixOS modules of filnix's own Nixpkgs:
          # the Fil-C ports (systemd's above all) are built and tested
          # against those, not against another release's.
          lib.nixosSystem =
            args:
            import "${nixpkgs}/nixos/lib/eval-config.nix" (
              {
                system = null;
              }
              // args
              // {
                modules = [
                  self.nixosModules.default
                  { filc.enable = nixlib.mkDefault true; }
                ]
                ++ args.modules or [ ];
              }
            );

          # The base machine of the images; see nixos/base.nix.
          nixosModules.base = import ./nixos/base.nix { filnix = self; };
          nixosConfigurations.base = self.lib.nixosSystem {
            modules = [ self.nixosModules.base ];
          };
          # The same machine on EC2, for the public AMI; see nixos/amazon.nix.
          nixosConfigurations.amazon = self.lib.nixosSystem {
            modules = [ (import ./nixos/amazon.nix { filnix = self; }) ];
          };
          # https://filc.less.rest, on that AMI; see nixos/demo-wiki.nix.
          nixosConfigurations.demo-wiki = self.lib.nixosSystem {
            modules = [ (import ./nixos/demo-wiki.nix { filnix = self; }) ];
          };

          # The finix machine with a Fil-C userland; see finix/demo.nix.
          finixConfigurations.filc-demo = (import finix).lib.finixSystem {
            lib = nixlib;
            modules = [
              self.finixModules.default
              "${finix}/modules/virtualisation/qemu.nix"
              ./finix/demo.nix
              { filc.system = system; }
            ];
          };

          # Export the full cross-compiled package sets
          legacyPackages.${system} = {
            inherit pkgsFilc pkgsFilcStaging pkgsFilcSystem;
            # A package set, not a derivation; .#rubyWithGem.<gem> still works.
            inherit rubyWithGem;
            # NixOS VM tests of Fil-C systems; see tests/nixos/default.nix.
            nixosTests = import ./tests/nixos {
              inherit pkgs pkgsFilc;
              filcModule = self.nixosModules.default;
              filnix = self;
            };
          };

          packages.${system} =
            nixlib.optionalAttrs (system == "x86_64-linux") {
              # The base Fil-C NixOS as a compressed qcow2, and a VM that
              # boots it (nixos/image.nix).
              nixos-image = nixosImage.image;
              nixos-vm = nixosImage.vm;
              # Its EC2 variant as a VHD, which .github/workflows/ami.yml imports.
              nixos-ami = self.nixosConfigurations.amazon.config.system.build.ami;
            }
            // {
              default = filcc;
              baseline = baseline.baseline;
              # Fil-C, runtime and native ELF files in a closure (docs/nixos.md).
              filc-audit = pkgs.writeShellApplication {
                name = "filc-audit";
                runtimeInputs = [
                  pkgs.binutils-unwrapped
                  pkgs.findutils
                ];
                text = builtins.readFile ./lib/filc-audit.sh;
              };
              baseline-shell = baseline.shell;
              inherit
                filcc
                filcc-staging
                projeny
                sarcasm
                sarcasm-prolog
                zstd-sarcasm
                ;
              inherit (sarcasm) minilute;
              inherit (pkgsFilc) openssl-sarcasm;
              php-dist = import ./packages/php-dist { inherit pkgs pkgsFilc; };
              # Vulnerable PHP for reproductions, never the default or :latest.
              php84_25 = pkgsFilcPhp84_25.php84_25;
              php84_25-dist = import ./packages/php-dist {
                inherit pkgs;
                pkgsFilc = pkgsFilcPhp84_25;
                base = pkgsFilcPhp84_25.php84_25;
              };
              php84_25-docker = import ./packages/php-dist/docker.nix {
                inherit pkgs;
                dist = self.packages.${system}.php84_25-dist;
              };
              # Experimental: opcache's JIT, compiled through C (docs/php.md).
              php-jit = pkgsFilc.php84-jit;
              # Native against Fil-C PHP 8.5 on real applications (bench/php).
              php-bench = import ./bench/php { inherit pkgs pkgsFilc pkgsFilcStaging; };
              # PHP 8.5 with the same JIT, on the staging toolchain.
              php85-jit = pkgsFilcStaging.php85-jit;
              php74-dist = import ./packages/php-dist {
                inherit pkgs pkgsFilc;
                php = pkgsFilc.php74.withExtensions (
                  { enabled, all }:
                  enabled
                  ++ (with all; [
                    bz2
                    shmop
                    sysvmsg
                    sysvshm
                  ])
                );
              };
              inherit optfil;
              filroot = import ./packages/filroot { inherit pkgs optfil; };
              # The GitHub Pages site: pages/ and the rendered docs/.
              site = import ./packages/site {
                inherit pkgs nixpkgs;
                filcc = filcc-staging;
                filnix = self;
              };
              # The site's SWI-Prolog 10, which nixpkgs does not have; ship
              # publishes it so the Pages build substitutes it.
              site-swipl = import ./nanofil/web/play/swipl.nix { inherit pkgs; };
              # The site's nanofil playground, built with the staging toolchain;
              # ship publishes it so Pages does not rebuild staging clang.
              site-play = self.packages.${system}.site.play;
              php-docker = import ./packages/php-dist/docker.nix {
                inherit pkgs;
                dist = import ./packages/php-dist { inherit pkgs pkgsFilc; };
              };
              bind-dist = import ./packages/bind-dist { inherit pkgs pkgsFilc; };
              bind-docker = import ./packages/bind-dist/docker.nix {
                inherit pkgs;
                dist = import ./packages/bind-dist { inherit pkgs pkgsFilc; };
              };
              # The PostgreSQL server with -fzmark-shared (docs/zmark-shared.md),
              # staging only; the campaign builds it (scripts/ci-outputs.txt).
              postgresql-staging-zmark = pkgsFilcStaging.postgresql_18;
              # Release alternates on the staging toolchain: unreleased compiler
              # and runtime changes, faster but less reviewed (docs/php.md).
              php85-staging-dist = import ./packages/php-dist {
                inherit pkgs;
                pkgsFilc = pkgsFilcStaging;
                base = pkgsFilcStaging.php85;
                suffix = "-staging";
              };
              php85-staging-docker = import ./packages/php-dist/docker.nix {
                inherit pkgs;
                dist = import ./packages/php-dist {
                  inherit pkgs;
                  pkgsFilc = pkgsFilcStaging;
                  base = pkgsFilcStaging.php85;
                  suffix = "-staging";
                };
              };
              bind-staging-dist = import ./packages/bind-dist {
                inherit pkgs;
                pkgsFilc = pkgsFilcStaging;
                suffix = "-staging";
              };
              bind-staging-docker = import ./packages/bind-dist/docker.nix {
                inherit pkgs;
                dist = import ./packages/bind-dist {
                  inherit pkgs;
                  pkgsFilc = pkgsFilcStaging;
                  suffix = "-staging";
                };
              };
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

              devtools = devtoolsFor pkgs;

              push-filcc = pkgs.writeShellScriptBin "push-filcc" ''
                ${pkgs.cachix}/bin/cachix push filc ${filcc}
              '';

              push-pkg = pkgs.writeShellScriptBin "push-pkg" ''
                for pkg in "$@"; do
                  ${pkgs.cachix}/bin/cachix push filc $(${pkgs.nix}/bin/nix build .#"$pkg" --print-out-paths --no-link)
                done
              '';

              inherit runfilc;

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
            filcc-staging = {
              type = "app";
              program = "${filcc-staging}/bin/clang";
            };

            "filc++" = {
              type = "app";
              program = "${filcc}/bin/clang++";
            };
            "filc++-staging" = {
              type = "app";
              program = "${filcc-staging}/bin/clang++";
            };
          };

          formatter.${system} = pkgs.nixfmt;

          devShells.${system} = {
            default = devShellFor pkgs projeny;

            # Full Fil-C compilation environment (opt-in with 'nix develop .#world')
            world = filc-world-shell;

            # Incremental Fil-C LLVM hacking; see docs/llvm-dev.md
            filc-llvm = import ./shells/filc-llvm.nix { inherit pkgs; };
            filc-llvm-staging = import ./shells/filc-llvm.nix {
              inherit pkgs;
              sources = stagingSources;
            };
          };
        };

      # Fil-C is Linux-only, but Macs still run the git hooks and scripts/ship
      # (which builds through a Linux builder or the publisher host), so they
      # get the host tools those need and the default dev shell.
      hostTools =
        system:
        let
          pkgs = import nixpkgs { inherit system; };
          projeny = pkgs.callPackage ./packages/projeny.nix { };
        in
        {
          packages.${system} = {
            inherit projeny;
            devtools = devtoolsFor pkgs;
          };
          formatter.${system} = pkgs.nixfmt;
          devShells.${system}.default = devShellFor pkgs projeny;
        };

      # What scripts/git-hooks and scripts/ship run, so that they work
      # without nix develop.
      devtoolsFor =
        pkgs:
        pkgs.buildEnv {
          name = "filnix-devtools";
          paths = with pkgs; [
            treefmt
            nixfmt
            actionlint
            shellcheck
            python3
            git
          ];
        };

      devShellFor =
        pkgs: projeny:
        pkgs.mkShell {
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
    in
    nixlib.foldl' nixlib.recursiveUpdate { } [
      (hostTools "aarch64-darwin")
      (hostTools "x86_64-darwin")
      (builtins.removeAttrs (perSystem "aarch64-linux") [
        "overlays"
        "nixosModules"
        "nixosConfigurations"
        "finixModules"
        "finixConfigurations"
      ])
      (perSystem "x86_64-linux")
    ];
}
