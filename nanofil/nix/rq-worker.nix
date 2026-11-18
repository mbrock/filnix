# This file builds the worker behind rq, the persistent Rocq proof session.
# The worker is an Eio program that links Rocq's parser and interpreter and
# keeps one session alive behind a Unix socket. It uses the Rocq, OCaml and
# findlib of rocq-packages.nix, so a session loads the same objects that
# one.sh compiles. The rq command builds it on first use.
#
# The worker needs Eio 1.7, which is newer than the 1.3 of the pinned
# nixpkgs. Eio 1.7 brings Eio_unix.set_signal, which the worker uses for
# its interrupt handler, and its io_uring backend needs uring 2.15.1. Both
# overrides stay inside the worker's own OCaml package scope, so Rocq and
# its libraries are not rebuilt.
{ pkgs }:
let
  rocq = import ./rocq-packages.nix { inherit pkgs; };
  ocamlPackages = rocq.rocq-core.ocamlPackages.overrideScope (
    final: prev: {
      uring = prev.uring.overrideAttrs {
        name = "ocaml${final.ocaml.version}-uring-2.15.1";
        version = "2.15.1";
        src = pkgs.fetchurl {
          url = "https://github.com/ocaml-multicore/ocaml-uring/releases/download/v2.15.1/uring-2.15.1.tbz";
          hash = "sha256-j7ivQPKDbOIqjycknQsSI+eQjrAv3U66tWmEIUTdwLE=";
        };
      };
      eio = prev.eio.overrideAttrs (old: {
        name = "ocaml${final.ocaml.version}-eio-1.7";
        version = "1.7";
        src = pkgs.fetchurl {
          url = "https://github.com/ocaml-multicore/eio/releases/download/v1.7/eio-1.7.tbz";
          hash = "sha256-qXccDX9NnZ/he63T0UfJboXzRBCrJSEZreKkB6tBzLU=";
        };
        patches = [ ];
        buildInputs = (old.buildInputs or [ ]) ++ [ final.dune-configurator ];
        doCheck = false;
      });
      # Eio 1.7 shares a configure step between eio and its backends.
      eio_linux = prev.eio_linux.overrideAttrs (old: {
        buildInputs = (old.buildInputs or [ ]) ++ [ final.dune-configurator ];
      });
    }
  );
in
ocamlPackages.buildDunePackage {
  pname = "rq-worker";
  version = "0";
  src = ../rocq/scripts/glibc-tools/rq/worker;
  buildInputs = [
    rocq.rocq-core
    ocamlPackages.eio_main
    ocamlPackages.yojson
    ocamlPackages.findlib
    ocamlPackages.zarith
  ];
  passthru.eio = ocamlPackages.eio;
}
