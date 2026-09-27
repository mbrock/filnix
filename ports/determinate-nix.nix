# Determinate Systems' Nix fork (github.com/DeterminateSystems/nix-src),
# built with Fil-C. Nixpkgs has no package for it, so this instantiates the
# fork's own component scope (packaging/components.nix, the same structure
# Nixpkgs vendors for upstream Nix) on top of Nixpkgs' `nixDependencies`,
# then applies the Fil-C overrides shared with the upstream Nix port.
# See docs/determinate-nix.md.
{
  pkgs,
  final,
  nixFilcOverrides,
}:
let
  inherit (pkgs) lib;
  version = "3.22.5";
  src = builtins.fetchTarball {
    name = "determinate-nix-src-${version}";
    url = "https://github.com/DeterminateSystems/nix-src/archive/v${version}.tar.gz";
    sha256 = "sha256-5rX9rK1y8NpOaYyL+cn1P2O5re+ON2Wpo39J8/LLCXI=";
  };
  scope = lib.makeScope final.nixDependencies.newScope (
    import "${src}/packaging/components.nix" {
      inherit lib src;
      pkgs = final;
      officialRelease = true;
      maintainers = [ ];
    }
  );
in
((scope.overrideSource src).appendPatches [
  ../patches/determinate-nix/0001-Fil-C-pointer-typed-packed-Value-words.patch
  ../patches/determinate-nix/0002-Fil-C-no-__cxa_throw-interposer.patch
  ../patches/determinate-nix/0003-Fil-C-truncate-syscall-results-to-int.patch
  ../patches/determinate-nix/0004-Fil-C-smaller-symbol-arena-no-bump-allocator-reserva.patch
  ../patches/determinate-nix/0005-Unmap-the-symbol-table-s-arena-when-the-table-is-des.patch
]).overrideScope
  (
    lib.composeExtensions nixFilcOverrides (
      nfinal: nprev: {
        # Unity builds compile each library as one translation unit, which
        # serializes the (slow) Fil-C compile.
        withUnityBuild = false;
        # The fork's libgit2 (a 2.0 pre-release with in-memory config
        # backends, which libfetchers needs), on top of the libgit2 port.
        inherit
          (import "${src}/packaging/dependencies.nix" {
            inputs = { };
            pkgs = final;
            inherit (final) stdenv;
          } nfinal)
          libgit2
          ;
        # The fork's store layer uses Boost.Asio, whose io_context executor
        # keeps its context pointer (plus flag bits) in a uintptr_t. Kept to
        # this scope so the rest of pkgsFilc keeps its cached Boost.
        boost = final.boost.overrideAttrs (old: {
          patches = (old.patches or [ ]) ++ [ ../patches/boost-asio-io-context-executor-pointer.patch ];
        });
        # Wasm support needs wasmtime (Rust with Cranelift's JIT), and crash
        # reporting sentry-native with crashpad; both are off.
        wasmtime = null;
        # nix-cli enables Sentry unconditionally; its flags are dropped below.
        sentry-native = final.emptyDirectory;
        nix-expr = nprev.nix-expr.override {
          enableGC = false;
          enableWasm = false;
        };
        nix-store = nprev.nix-store.override { enableWasm = false; };
        nix-cli =
          (nprev.nix-cli.override {
            # Fil-C has its own allocator and GC; mimalloc replacing malloc
            # would bypass it.
            withMimalloc = false;
          }).overrideAttrs
            (old: {
              buildInputs = lib.remove final.emptyDirectory old.buildInputs;
              mesonFlags = map (flag: if flag == "-Dsentry=enabled" then "-Dsentry=disabled" else flag) (
                lib.filter (flag: !lib.hasPrefix "-Dcrashpad-handler=" flag) old.mesonFlags
              );
            });
        # This scope is not spliced, so the `enosys` wrapper (a seccomp
        # filter, which Fil-C cannot install) would be the Fil-C build.
        nix-util-tests =
          (nprev.nix-util-tests.override {
            util-linux = final.buildPackages.util-linux;
          }).overrideAttrs
            (old: {
              passthru = old.passthru // {
                tests = lib.mapAttrs (
                  _: run:
                  run.overrideAttrs {
                    # An exception thrown through libarchive's read callback
                    # is freed while still unwinding (docs/filc-findings.md),
                    # as in the upstream Nix port.
                    GTEST_FILTER = "-CompressionDecompression/CompressionDecompressionTest.invalidDecompression/*";
                  }
                ) old.passthru.tests;
              };
            });
        nix-functional-tests = nprev.nix-functional-tests.override {
          util-linux = final.buildPackages.util-linux;
        };
        # The functional tests again, with every evaluation multi-threaded
        # (and builtins.parallel available). Not part of nix-everything.
        nix-functional-tests-parallel = nfinal.nix-functional-tests.overrideAttrs (old: {
          pname = "nix-functional-tests-parallel";
          _NIX_TEST_EXTRA_CONFIG = ''
            ${old._NIX_TEST_EXTRA_CONFIG or ""}
            eval-cores = 8
            extra-experimental-features = parallel-eval
          '';
        });
        # And with lazy trees, as the fork's CI runs them.
        nix-functional-tests-lazy-trees = nfinal.nix-functional-tests.override {
          pname = "nix-functional-tests-lazy-trees";
          lazyTrees = true;
        };
        # Boehm GC is only referenced to collect its debug output.
        nix-everything = nprev.nix-everything.override { boehmgc = final.emptyDirectory; };
      }
    )
  )
