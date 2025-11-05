{
  base,
  lib,
  runtime,
  compiler,
}:

let
  inherit (lib) mergeLayers addLibcMetadata;
  inherit (runtime) libyolo libpizlo libmojo;
  inherit (compiler) filc-libcxx;

in
{
  filc-sysroot =
    addLibcMetadata
      (mergeLayers "filc-sysroot" [
        libyolo
        libpizlo
        libmojo
        filc-libcxx
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
      };
}
