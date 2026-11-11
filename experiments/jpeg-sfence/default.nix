# This experiment changes only the assembler's SFENCE classification.
let
  previous = import ../zstd-fast-flags/default.nix;
  inherit (previous) pkgs filcc;
  oldAssembler = previous.newAssembler;
  newAssembler = oldAssembler.overrideAttrs {
    src = pkgs.fetchgit {
      name = "sarcasm-src";
      url = "https://github.com/mbrock/fil-c";
      rev = "1f869d1c15a797876c1ac3287eaf599a4e1cc8b3";
      hash = "sha256-Dbs0m/yg6r09Jv4/SxNIR6dM71GZ27qtrV17g31oAXo=";
      sparseCheckout = [ "projects/sarcasm" ];
    };
    version = "0-unstable-1f869d1c15a7";
  };
in
{
  inherit
    pkgs
    filcc
    oldAssembler
    newAssembler
    ;
}
