{
  pkgs,
  filc,
}:

let
  lib = import ../lib { inherit pkgs; };
  inherit (lib) mergeLayers addLibcMetadata;
  inherit (filc)
    yolo-glibc
    libpizlo
    filc-glibc
    filc-libcxx
    ;

in
addLibcMetadata
  (mergeLayers "filc-sysroot" [
    yolo-glibc
    libpizlo
    filc-glibc
    filc-libcxx
    pkgs.linuxHeaders
  ])
  {
    dynamicLinker = "ld-yolo-x86_64.so";
    crts = [
      "crt1.o"
      "rcrt1.o"
      "Scrt1.o"
      "crti.o"
      "crtn.o"
    ];
  }
