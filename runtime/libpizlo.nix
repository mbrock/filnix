{
  pkgs,
  filc,
  compiler-rt,
  sources ? import ../lib/sources.nix { inherit pkgs; },
  # The LLVM JIT shim (runtime/llvmjit.nix), for pins that have the JIT.
  llvmjit ? null,
}:

let
  lib = import ../lib { inherit pkgs; };
  inherit (lib) setupCcache base-clang;

in
{

  # Build libpizlo (Fil-C runtime library - GC + memory safety)
  # Use the original Makefile - it knows which files to build
  libpizlo = pkgs.stdenv.mkDerivation {
    pname = "libpizlo";
    version = "git";
    src = sources.libpas-src;
    patches = [
      # prctl's capability options returned ENOSYS, so systemd could start no service.
      ../patches/filc-runtime-prctl-caps.patch
    ]
    # Staging already has this fix; the official releases do not.
    ++ pkgs.lib.optional (
      sources.variant == "release"
    ) ../patches/fil-c/runtime-exception-unwind.patch
    # zsys_brk reports the program break, so sbrk(0) works as it does natively.
    ++ [ ../patches/filc-runtime-brk-query.patch ]
    # Proof of concept: zclosure_new_sealed (docs/sealed-closures.md).
    ++ pkgs.lib.optional (
      sources.variant == "staging"
    ) ../patches/fil-c/sealed-closures.patch
    # zmark_shared: shared mappings whose pointers hold addresses only (docs/zmark-shared.md).
    # Staging only; the pass half is in compiler/filc0.nix.
    ++ pkgs.lib.optional (
      sources.variant == "staging"
    ) ../patches/fil-c/runtime-zmark-shared.patch;

    nativeBuildInputs = [
      pkgs.gnumake
      pkgs.ruby
      base-clang
      filc
      pkgs.ccache
    ]
    ++ pkgs.lib.optional (sources.llvmjit-src != null) pkgs.python3;

    # Under glibc, libpas includes filc/llvmjit/filc_llvm_jit_api.h, which is
    # generated from LLVM's C API headers.
    preConfigure =
      pkgs.lib.optionalString (sources.llvmjit-src != null) ''
        cp -r --no-preserve=mode ${sources.llvmjit-src}/. .
        python3 filc/llvmjit/gen_filc_llvm_jit_header.py
      ''
      + ''
        cd libpas
        ${setupCcache}
        export CC="ccache clang"
        export FILC_CLANG="${filc}/bin/clang"
        # These env vars are for the Makefile to find libraries/headers
        export FILC_YOLO_INCLUDE="${filc.libyolo-impl}/include"
        export FILC_OS_INCLUDE="${pkgs.linuxHeaders}/include"
        export FILC_STDFIL_INCLUDE="$PWD/../filc/include"
        export FILC_INCLUDE_DIR="${filc.libyolo-impl}/include"
        export FILC_YOLO_LIB_DIR="${filc.libyolo}/lib"
        export FILC_DYNAMIC_LINKER="${filc.libyolo}/lib/${lib.dynamicLinker}"
        PIZFIX_OUT="$PWD/pizfix"
        export FILC_LIB_DIR="$PIZFIX_OUT/lib"
        export FILC_LIB_TEST_DIR="$PIZFIX_OUT/lib_test"
        export FILC_LIB_GCVERIFY_DIR="$PIZFIX_OUT/lib_gcverify"
        export FILC_LIB_TEST_GCVERIFY_DIR="$PIZFIX_OUT/lib_test_gcverify"
        mkdir -p "$FILC_LIB_DIR" "$FILC_LIB_TEST_DIR" "$FILC_LIB_GCVERIFY_DIR" "$FILC_LIB_TEST_GCVERIFY_DIR"
        cp ${compiler-rt}/lib/crtbegin.o "$FILC_LIB_DIR"/
        cp ${compiler-rt}/lib/crtend.o "$FILC_LIB_DIR"/
        cp ${compiler-rt}/lib/libyolort.a "$FILC_LIB_DIR"/
        patchShebangs .
      '';

    buildPhase = ''
      mkdir -p build
      ${pkgs.ruby}/bin/ruby src/libpas/generate_pizlonated_forwarders.rb src/libpas/filc_native.h
      make -j$NIX_BUILD_CORES FILCFLAGS="-O3 -g -W -Werror -Wno-unused-command-line-argument -MD -I../filc/include"${
        pkgs.lib.optionalString (llvmjit != null)
          " \"HOST_CLANG=clang -DFILC_LLVMJIT_SO_PATH='\\\"${llvmjit}/lib/libfilcllvmjit.so\\\"'\""
      }
    '';

    installPhase = ''
      mkdir -p $out/lib $out/include
      cp "$FILC_LIB_DIR"/libpizlo.so $out/lib/
      cp "$FILC_LIB_DIR"/libpizlo.a $out/lib/
      cp "$FILC_LIB_DIR"/filc_crt.o $out/lib/
      cp "$FILC_LIB_DIR"/filc_mincrt.o $out/lib/
    ''
    + pkgs.lib.optionalString (llvmjit != null) ''
      cp "$FILC_LIB_DIR"/filc_jit_crt.o $out/lib/
      cp "$FILC_LIB_DIR"/filc_jit_mincrt.o $out/lib/
    ''
    + ''
      cp ../filc/include/*.h $out/include/
    '';

    enableParallelBuilding = true;
    passthru = { inherit llvmjit; };
    meta.description = "Fil-C runtime library (libpizlo)";
  };
}
