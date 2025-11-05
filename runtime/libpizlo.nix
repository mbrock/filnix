{
  base,
  lib,
  sources,
  filc1-runtime,
  libyolo-glibc,
  libyolo,
  filc-stdfil-headers,
}:

let
  inherit (lib) setupCcache base-clang;

in
rec {

  # Build libpizlo (Fil-C runtime library - GC + memory safety)
  # Use the original Makefile - it knows which files to build
  libpizlo = base.stdenv.mkDerivation {
    pname = "libpizlo";
    version = "git";
    src = sources.libpas-src;

    nativeBuildInputs = [
      base.gnumake
      base.ruby
      base-clang
      filc1-runtime
      base.ccache
    ];

    preConfigure = ''
      cd libpas
      ${setupCcache}
      export CC="ccache clang"
      export FILC_CLANG="${filc1-runtime}/bin/clang"
      export FILC_YOLO_INCLUDE="${libyolo-glibc}/include"
      export FILC_OS_INCLUDE="${base.linuxHeaders}/include"
      export FILC_STDFIL_INCLUDE="${filc-stdfil-headers}"
      export FILC_INCLUDE_DIR="${libyolo-glibc}/include"
      export FILC_YOLO_LIB_DIR="${libyolo}/lib"
      export FILC_DYNAMIC_LINKER="${libyolo}/lib/ld-yolo-x86_64.so"
      PIZFIX_OUT="$PWD/pizfix"
      export FILC_LIB_DIR="$PIZFIX_OUT/lib"
      export FILC_LIB_TEST_DIR="$PIZFIX_OUT/lib_test"
      export FILC_LIB_GCVERIFY_DIR="$PIZFIX_OUT/lib_gcverify"
      export FILC_LIB_TEST_GCVERIFY_DIR="$PIZFIX_OUT/lib_test_gcverify"
      mkdir -p "$FILC_LIB_DIR" "$FILC_LIB_TEST_DIR" "$FILC_LIB_GCVERIFY_DIR" "$FILC_LIB_TEST_GCVERIFY_DIR"
      patchShebangs .
    '';

    buildPhase = ''
      mkdir -p build
      ${base.ruby}/bin/ruby src/libpas/generate_pizlonated_forwarders.rb src/libpas/filc_native.h
      make -j$NIX_BUILD_CORES FILCFLAGS="-O3 -g -W -Werror -Wno-unused-command-line-argument -MD -I../filc/include"
    '';

    installPhase = ''
      mkdir -p $out/lib $out/include
      cp "$FILC_LIB_DIR"/libpizlo.so $out/lib/
      cp "$FILC_LIB_DIR"/libpizlo.a $out/lib/
      cp "$FILC_LIB_DIR"/filc_crt.o $out/lib/
      cp "$FILC_LIB_DIR"/filc_mincrt.o $out/lib/
      cp ../filc/include/*.h $out/include/
    '';

    enableParallelBuilding = true;
    meta.description = "Fil-C runtime library (libpizlo)";
  };
}
