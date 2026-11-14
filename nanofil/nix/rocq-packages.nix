# Rocq 9.3.0 with stdlib 9.2.0, std++ bd38c741 and Iris 7e9583b2, built
# with OCaml 5.4.1 from the repository's own nixpkgs. Only the Nanofil
# proof derivations (rocq.nix, glibc.nix) and the proof-eng scripts use
# these packages, so the Fil-C toolchain and nixpkgs pin are unchanged.
#
# The native compiler is enabled in ondemand mode: files compile to .vo
# only, as before, and native_compute compiles the code it needs when it
# runs. std++ and Iris come over git: gitlab.mpi-sws.org throttles its
# archive downloads (HTTP 429), and name = "source" keeps the store paths
# the archives had. A derivation that runs native_compute needs this rocq-core's OCaml
# and findlib among its inputs, since native code is linked with ocamlopt.
{ pkgs }:
pkgs.rocqPackages_9_2.overrideScope (
  final: prev: {
    rocq-core =
      (prev.rocq-core.override { rocq-version = "9.3"; }).overrideAttrs
        {
          version = "9.3.0";
          configureFlags = [
            "-native-compiler"
            "ondemand"
          ];
          src = pkgs.fetchzip {
            url = "https://github.com/rocq-prover/rocq/archive/c8e202eb0d6cc08b848ba27dcf2cc35804df7d96.tar.gz";
            hash = "sha256-Wr9+5Mq3/hS3gnyZDnzBo9aJCjeqQDGi4eaU1LinwaE=";
          };
        };
    stdlib = (prev.stdlib.override { version = "9.1.0"; }).overrideAttrs {
      version = "9.2.0";
      src = pkgs.fetchzip {
        url = "https://github.com/rocq-prover/stdlib/archive/8dd155bc10529814202f8f4c643e5ae6c2c88fa6.tar.gz";
        hash = "sha256-ySNY8XUQOH6B1B2p+39jdJ7UjIMrRDl499JJwpLEHuM=";
      };
    };
    stdpp = (prev.stdpp.override { version = "1.13.0"; }).overrideAttrs {
      version = "dev-bd38c741";
      src = pkgs.fetchgit {
        name = "source";
        url = "https://gitlab.mpi-sws.org/iris/stdpp.git";
        rev = "bd38c741cac9bb9803a322f2a69c794ae1407e76";
        hash = "sha256-VfvcmGELcRDMqVLupaAyMb6RXarDNo2iCSCsbX2xPjA=";
      };
      buildPhase = "./make-package stdpp -j$NIX_BUILD_CORES";
      installPhase = "./make-package stdpp install $installFlags";
    };
    iris = (prev.iris.override { version = "4.5.0"; }).overrideAttrs {
      version = "dev-7e9583b2";
      src = pkgs.fetchgit {
        name = "source";
        url = "https://gitlab.mpi-sws.org/iris/iris.git";
        rev = "7e9583b2af18fd82b44b6a33d447146e37da67ca";
        hash = "sha256-R6hllx9eoNg/E6il9qBzYkkpLnhnP71pWvVHI+GtC1w=";
      };
      buildPhase = "./make-package iris -j$NIX_BUILD_CORES";
      installPhase = "./make-package iris install $installFlags";
    };
  }
)
