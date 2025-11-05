{
  base,
  lib,
  filc0,
  libyolo,
  libyolo-glibc,
  libpizlo,
  filc-stdfil-headers,
}:

let
  inherit (lib)
    gcc
    llvmMajor
    targetPlatform
    gcc-lib
    ;

  # Build CRT library directory (libyolo + gcc crt files + optional filc runtime)
  mkFilcCrtLib =
    {
      filcRuntimeLibs ? null,
    }:
    base.runCommand "filc-crt-lib"
      {
        nativeBuildInputs = [ base.rsync ];
      }
      ''
        mkdir -p $out

        # Libraries: yolo + gcc crt files + optional filc runtime
        rsync -a ${libyolo}/lib/ $out/
        chmod -R u+w $out
        cp ${gcc-lib}/crt*.o $out/
        cp ${gcc-lib}/libgcc* $out/ || true
        mkdir -p $out/gcc/${targetPlatform}/${gcc.version}
        cp -r ${gcc-lib}/* $out/gcc/${targetPlatform}/${gcc.version}/

        ${base.lib.optionalString (filcRuntimeLibs != null) ''
          cp ${filcRuntimeLibs}/lib/filc_crt.o $out/ || true
          cp ${filcRuntimeLibs}/lib/filc_mincrt.o $out/ || true
          cp ${filcRuntimeLibs}/lib/libpizlo.so $out/ || true
          cp ${filcRuntimeLibs}/lib/libpizlo.a $out/ || true
        ''}
      '';

  # Assemble Fil-C compiler with explicit flags instead of pizfix directory layout
  mkFilcClang =
    {
      crtLib,
      yoloInclude,
      osInclude,
      stdfilInclude,
    }:
    base.runCommand "filc"
      {
        nativeBuildInputs = [ base.makeWrapper ];
      }
      ''
        mkdir -p $out/bin

        # Wrap clang with Fil-C paths using explicit flags
        makeWrapper ${filc0}/bin/clang-${llvmMajor} $out/bin/clang \
          --add-flags "-Wno-unused-command-line-argument" \
          --add-flags "--gcc-toolchain=${gcc.cc}" \
          --add-flags "-resource-dir ${filc0}/lib/clang/${llvmMajor}" \
          --add-flags "--filc-dynamic-linker=${crtLib}/ld-yolo-x86_64.so" \
          --add-flags "--filc-crt-path=${crtLib}" \
          --add-flags "--filc-stdfil-include=${stdfilInclude}" \
          --add-flags "--filc-os-include=${osInclude}" \
          --add-flags "--filc-include=${yoloInclude}"

        ln -s clang $out/bin/clang++
      '';

in
{
  inherit mkFilcCrtLib mkFilcClang;

  # Second compiler stage adds the Fil-C runtime, compiled using filc1.
  filc2 = mkFilcClang {
    crtLib = mkFilcCrtLib { filcRuntimeLibs = libpizlo; };
    yoloInclude = "${libyolo-glibc}/include";
    osInclude = "${base.linuxHeaders}/include";
    stdfilInclude = filc-stdfil-headers;
  };
}
