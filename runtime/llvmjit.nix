# libfilcllvmjit.so, the native shim behind Fil-C's LLVM JIT API, built the
# way upstream's libpas/build_llvmjit.sh builds it. libpizlo dlopens it on the
# first JIT call; its LLVM includes the Fil-C passes, which run on every
# module the JIT compiles.
{
  pkgs,
  filc0,
  src,
}:

pkgs.stdenv.mkDerivation {
  pname = "filc-llvmjit";
  version = "git";
  inherit src;

  nativeBuildInputs = [ pkgs.python3 ];

  buildPhase = ''
    runHook preBuild
    python3 filc/llvmjit/gen_filc_llvm_jit_header.py

    # LLVM was built without RTTI and exceptions, so the shim must match.
    $CXX -g -O2 -fPIC -fvisibility=hidden -fno-rtti -fno-exceptions -std=c++20 \
      -I ${filc0.dev}/include -Wno-deprecated-declarations \
      -c filc/llvmjit/filc_llvm_jit_shim.cpp -o shim.o

    # Fil-C processes have no host libstdc++ or libc to load, so link the C++
    # runtime statically with no shared NEEDEDs; libc references bind to the
    # hosting process's yolo glibc.
    $CXX -g -shared -nodefaultlibs -o libfilcllvmjit.so shim.o \
      -Wl,--version-script=filc/llvmjit/filc_llvm_jit_shim.version \
      -Wl,--exclude-libs,ALL \
      -Wl,--start-group ${filc0.dev}/lib/libLLVM*.a -Wl,--end-group \
      "$($CXX -print-file-name=libstdc++.a)" \
      "$($CXX -print-file-name=libgcc_eh.a)" \
      "$($CXX -print-file-name=libgcc.a)"
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    install -Dm755 libfilcllvmjit.so $out/lib/libfilcllvmjit.so
    runHook postInstall
  '';

  # The shim must not depend on the host's glibc or libstdc++ at run time.
  dontPatchELF = true;
  preFixup = ''
    if readelf -d $out/lib/libfilcllvmjit.so | grep -q NEEDED; then
      readelf -d $out/lib/libfilcllvmjit.so | grep NEEDED
      echo "libfilcllvmjit.so must have no NEEDED entries" >&2
      exit 1
    fi
  '';

  meta.description = "Fil-C LLVM JIT shim (libfilcllvmjit.so)";
}
