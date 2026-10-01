# Exercise the installed allocator and encoder, including the capability-bearing
# allocation header shared by lookahead, partitioning and coefficient buffers.
{ pkgs }:
pkgs.stdenv.mkDerivation {
  name = "filc-libaom-allocation-encoder-check";
  dontUnpack = true;
  buildPhase = ''
    # The allocator is private API, available in the installed static archive.
    $CC -Werror ${./libaom-allocation.c} ${pkgs.libaom.static}/lib/libaom.a -o allocation-check
  '';
  doCheck = true;
  checkPhase = ''
    ./allocation-check
    ${pkgs.buildPackages.python3}/bin/python3 ${./libaom-encoder.py} ${pkgs.libaom.bin}/bin
  '';
  installPhase = ''touch "$out"'';
}
