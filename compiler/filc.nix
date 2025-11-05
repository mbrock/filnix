{
  pkgs,
  filc0,
  yolo,
  libpizlo ? null,
  filc-libc ? null,
  filc-libcxx ? null,
}:

let
  lib = import ../lib { inherit pkgs; };
  sources = import ../lib/sources.nix { inherit pkgs; };
  inherit (lib)
    gcc
    llvmMajor
    targetPlatform
    gcc-lib
    ;

  inherit (yolo) yolo-glibc yolo-glibc-impl;

  filc-stdfil-headers = "${sources.libpas-src}/filc/include";

  # Build CRT library directory
  crtLib =
    pkgs.runCommand "filc-crt-lib"
      {
        nativeBuildInputs = [ pkgs.rsync ];
      }
      ''
        mkdir -p $out

        # Base: yolo-glibc libs + gcc crt files
        rsync -a ${yolo-glibc}/lib/ $out/
        chmod -R u+w $out
        cp ${gcc-lib}/crt*.o $out/
        cp ${gcc-lib}/libgcc* $out/ || true
        mkdir -p $out/gcc/${targetPlatform}/${gcc.version}
        cp -r ${gcc-lib}/* $out/gcc/${targetPlatform}/${gcc.version}/

        # Add libpizlo if available
        ${pkgs.lib.optionalString (libpizlo != null) ''
          cp ${libpizlo}/lib/filc_crt.o $out/ || true
          cp ${libpizlo}/lib/filc_mincrt.o $out/ || true
          cp ${libpizlo}/lib/libpizlo.so $out/ || true
          cp ${libpizlo}/lib/libpizlo.a $out/ || true
        ''}
      '';

  # Assemble the wrapper with appropriate flags
  wrapper =
    pkgs.runCommand "filc"
      {
        nativeBuildInputs = [ pkgs.makeWrapper ];
      }
      ''
        mkdir -p $out/bin

        # Base wrapper for C compiler
        makeWrapper ${filc0}/bin/clang-${llvmMajor} $out/bin/clang \
          --add-flags "-Wno-unused-command-line-argument" \
          --add-flags "--gcc-toolchain=${gcc.cc}" \
          --add-flags "-resource-dir ${filc0}/lib/clang/${llvmMajor}" \
          --add-flags "--filc-dynamic-linker=${crtLib}/ld-yolo-x86_64.so" \
          --add-flags "--filc-crt-path=${crtLib}" \
          --add-flags "--filc-stdfil-include=${filc-stdfil-headers}" \
          --add-flags "--filc-os-include=${pkgs.linuxHeaders}/include" \
          --add-flags "--filc-include=${yolo-glibc-impl}/include" \
        ${pkgs.lib.optionalString (filc-libc != null) ''
          --add-flags "-isystem ${filc-libc}/include" \
          --add-flags "-L${filc-libc}/lib"
        ''}

        # C++ wrapper
        ${
          if filc-libcxx != null then
            ''
              makeWrapper ${filc0}/bin/clang-${llvmMajor} $out/bin/clang++ \
                --add-flags "-Wno-unused-command-line-argument" \
                --add-flags "--gcc-toolchain=${gcc.cc}" \
                --add-flags "-resource-dir ${filc0}/lib/clang/${llvmMajor}" \
                --add-flags "--filc-dynamic-linker=${crtLib}/ld-yolo-x86_64.so" \
                --add-flags "--filc-crt-path=${crtLib}" \
                --add-flags "--filc-stdfil-include=${filc-stdfil-headers}" \
                --add-flags "--filc-os-include=${pkgs.linuxHeaders}/include" \
                --add-flags "--filc-include=${yolo-glibc-impl}/include" \
                ${
                  pkgs.lib.optionalString (filc-libc != null) ''
                    --add-flags "-isystem ${filc-libc}/include" \
                    --add-flags "-L${filc-libc}/lib" \
                  ''
                }\
                --add-flags "-nostdinc++" \
                --add-flags "-I${filc-libcxx}/include/c++" \
                --add-flags "-L${filc-libcxx}/lib"
            ''
          else
            ''
              ln -s clang $out/bin/clang++
            ''
        }
      '';

in
wrapper
// {
  # Expose yolo for modules that need it (like libpizlo's Makefile)
  # Use generic names so switching to musl later doesn't break the interface
  libyolo = yolo-glibc;
  libyolo-impl = yolo-glibc-impl;
}
