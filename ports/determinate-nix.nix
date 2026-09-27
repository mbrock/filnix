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
        nix-util-tests = nprev.nix-util-tests.override {
          util-linux = final.buildPackages.util-linux;
        };
        nix-functional-tests = nprev.nix-functional-tests.override {
          util-linux = final.buildPackages.util-linux;
        };
        # Boehm GC is only referenced to collect its debug output.
        nix-everything = nprev.nix-everything.override { boehmgc = final.emptyDirectory; };
      }
    )
  )
