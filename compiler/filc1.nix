{
  base,
  lib,
  filc0,
  libyolo-glibc,
  libyolo,
  filc-stdfil-headers,
}:

let
  inherit (lib) gcc llvmMajor;

in
rec {
  # From the bare compiler, we can create the first compiler stage,
  # which adds the basic yolo runtime and headers.
  # Keep it minimal - just the compiler, no extra wrapper flags
  filc1 =
    base.runCommand "filc1"
      {
        nativeBuildInputs = [ base.makeWrapper ];
      }
      ''
        mkdir -p $out/bin
        makeWrapper ${filc0}/bin/clang $out/bin/clang \
          --add-flags "--gcc-toolchain=${gcc.cc}" \
          --add-flags "-resource-dir ${filc0}/lib/clang/${llvmMajor}"
        ln -s clang $out/bin/clang++
      '';

  # Wrapper that bakes in yolo headers/libs so early builds (like libpizlo)
  # don't need to fabricate a pizfix tree.
  filc1-runtime =
    base.runCommand "filc1-runtime"
      {
        nativeBuildInputs = [ base.makeWrapper ];
      }
      ''
        mkdir -p $out/bin
        makeWrapper ${filc1}/bin/clang $out/bin/clang \
          --add-flags "--filc-dynamic-linker=${libyolo}/lib/ld-yolo-x86_64.so" \
          --add-flags "--filc-crt-path=${libyolo}/lib" \
          --add-flags "--filc-stdfil-include=${filc-stdfil-headers}" \
          --add-flags "--filc-os-include=${base.linuxHeaders}/include" \
          --add-flags "--filc-include=${libyolo-glibc}/include"
        ln -s clang $out/bin/clang++
      '';
}
