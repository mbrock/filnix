# This expression rebuilds OpenSSL with the experimental assembler and keeps
# the compiler and runtime pinned. The after build runs the full port test suite.
let
  repo = ../..;
  flake = builtins.getFlake (toString repo);
  pkgs = import flake.inputs.nixpkgs { system = "x86_64-linux"; };
  src = pkgs.fetchgit {
    name = "sarcasm-src";
    url = "https://github.com/mbrock/fil-c";
    rev = "7cafb5c30f5f126b38105cf179537d0244b313c3";
    sparseCheckout = [ "projects/sarcasm" ];
    hash = "sha256-ghIze8V5ZARF+a5ZOPV1aSFyf09sqSTWi3nSPNDkx60=";
  };
  sarcasm =
    (import ../../packages/sarcasm.nix { inherit pkgs; }).overrideAttrs
      {
        inherit src;
        version = "0-unstable-7cafb5c30f5";
      };
  before = flake.legacyPackages.x86_64-linux.pkgsFilc.openssl-sarcasm;
in
{
  inherit before sarcasm;
  after = before.overrideAttrs (old: {
    NIX_CFLAGS_COMPILE =
      (old.NIX_CFLAGS_COMPILE or "") + " --filc-resource-dir=${sarcasm}";
  });
}
