# zegarmistrz, the x86-64 emulator in upstream Fil-C that tracks poison
# bits (projects/zegarmistrz), built as its Makefile builds it. filnix
# does not package it yet; run.sh builds this file. With keepTaint, a
# tainted store keeps the taint (zegarmistrz-keep-taint.patch).
{
  pkgs,
  keepTaint ? false,
}:
pkgs.stdenv.mkDerivation rec {
  pname = "zegarmistrz" + pkgs.lib.optionalString keepTaint "-keep-taint";
  version = "0-unstable-9b7584cea1fa";
  src = pkgs.fetchgit {
    url = "https://github.com/pizlonator/fil-c";
    rev = "9b7584cea1fa0faf52ffec67859d3b7342919783";
    sparseCheckout = [ "projects/zegarmistrz" ];
    hash = "sha256-yKMAsBqz1mgwNumLfhFDzZ3rl9kQ28+nr7Xf00K9hjE=";
  };
  sourceRoot = "${src.name}/projects/zegarmistrz";
  patches = pkgs.lib.optional keepTaint ./zegarmistrz-keep-taint.patch;
  buildInputs = [
    pkgs.zydis
    pkgs.libbfd
    pkgs.libiberty
    pkgs.zlib
  ];
  dontConfigure = true;
  buildPhase = ''
    for f in src/*.cpp; do
      extra=
      if [ "$f" = src/stack_trace.cpp ]; then
        extra='-DPACKAGE="zegarmistrz" -DPACKAGE_VERSION="1"'
      fi
      $CXX -std=c++20 -O2 -g -Wall -D_GNU_SOURCE $extra -c -o "''${f%.cpp}.o" "$f" &
    done
    wait
    $CXX -o zegarmistrz src/*.o -pthread -lZydis -lZycore -lbfd
  '';
  installPhase = ''
    install -Dm755 zegarmistrz $out/bin/zegarmistrz
    install -Dm644 include/zegarmistrz.h $out/include/zegarmistrz.h
  '';
}
