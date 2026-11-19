# This package set builds Rocq 9.3.0, stdlib 9.2.0, std++ and Iris
# with OCaml 5.4.1 from the repository's own nixpkgs. Only the Nanofil
# proof derivations (rocq.nix, glibc.nix) and the glibc-tools scripts use
# these packages, so the Fil-C toolchain and nixpkgs pin are unchanged.
#
# The native compiler is enabled in ondemand mode: files compile to .vo
# only, as before, and native_compute compiles the code it needs when it
# runs. std++ and Iris come over git: gitlab.mpi-sws.org throttles its
# archive downloads (HTTP 429), and name = "source" keeps the store paths
# the archives had. A derivation that runs native_compute needs this rocq-core's OCaml
# and findlib among its inputs, since native code is linked with ocamlopt.
{ pkgs }:
let
  # The generated project now starts with a comment and a blank line.
  # Select its compiler flags explicitly when building an individual package.
  fixPackageFlags = ''
    substituteInPlace make-package \
      --replace-fail "sed -n '/./!q;p' _RocqProject | grep -E -v \"^-Q \"" \
        "grep '^-arg ' _RocqProject"
  '';
in
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
    # Iris and std++ keep the ssreflect spelling for Rocq releases before 9.3.
    rocq-cli = pkgs.symlinkJoin {
      name = "nanofil-rocq-${final.rocq-core.version}";
      paths = [ final.rocq-core ];
      postBuild = ''
        rm "$out/bin/rocq"
        ln -s ${pkgs.writeShellScript "nanofil-rocq" ''
          case "''${1-}" in
            c|compile|repl|top|repl-with-drop|top-with-drop)
              command=$1
              shift
              set -- "$command" -w -rewrite-rw "$@"
              ;;
          esac
          exec ${final.rocq-core}/bin/rocq "$@"
        ''} "$out/bin/rocq"
      '';
    };
    stdlib = (prev.stdlib.override { version = "9.1.0"; }).overrideAttrs {
      version = "9.2.0";
      src = pkgs.fetchzip {
        url = "https://github.com/rocq-prover/stdlib/archive/8dd155bc10529814202f8f4c643e5ae6c2c88fa6.tar.gz";
        hash = "sha256-ySNY8XUQOH6B1B2p+39jdJ7UjIMrRDl499JJwpLEHuM=";
      };
    };
    stdpp = (prev.stdpp.override { version = "1.13.0"; }).overrideAttrs {
      version = "dev-b4dc05b6";
      src = pkgs.fetchgit {
        name = "source";
        url = "https://gitlab.mpi-sws.org/iris/stdpp.git";
        rev = "b4dc05b6af93df9e0e9a9337ffb6c5a274b8df97";
        hash = "sha256-DPY3/Xl4JM4WOHexOuhj5b8oFKhnm/8wp983jOU/NWU=";
      };
      postPatch = fixPackageFlags;
      buildPhase = "./make-package stdpp -j$NIX_BUILD_CORES";
      installPhase = "./make-package stdpp install $installFlags";
    };
    iris = (prev.iris.override { version = "4.5.0"; }).overrideAttrs {
      version = "dev-2fe2f450";
      src = pkgs.fetchgit {
        name = "source";
        url = "https://gitlab.mpi-sws.org/iris/iris.git";
        rev = "2fe2f450add5678d9a2492343c638ccdb428a677";
        hash = "sha256-SW+y0p8/VloS6IGJg2mgRhCzL7g4CJZJqZQzvKAbikM=";
      };
      postPatch = fixPackageFlags;
      buildPhase = "./make-package iris -j$NIX_BUILD_CORES";
      installPhase = "./make-package iris install $installFlags";
    };
  }
)
