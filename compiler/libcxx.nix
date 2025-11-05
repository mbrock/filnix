{
  base,
  lib,
  sources,
  filc3,
  libmojo,
}:

let
  inherit (lib) mkFilcLLVMBuild;

in
{
  # Then we use filc3 to build libcxx!
  filc-libcxx =
    (mkFilcLLVMBuild {
      pname = "filc-libcxx";
      preConfigure = "";
      cmakeSource = "runtimes";
      buildDir = "build";
      ninjaTargets = [ ];
      customInstall = ''
        mkdir -p $out/lib $out/include
        cp -L build/lib/libc++*.{so,so.*,a} $out/lib/ || true
        cp -L build/lib/libc++abi*.{so,so.*,a} $out/lib/ || true
        cp -r build/include/c++/v1 $out/include/c++ || true

        # Fix RPATH to point to output lib directory
        for lib in $out/lib/*.so*; do
          [ -f "$lib" ] && patchelf --set-rpath "$out/lib" "$lib" || true
        done
      '';
      cmakeOptions = {
        LLVM_PATH = "../llvm";
        LLVM_ENABLE_RUNTIMES = "libcxx\\;libcxxabi";
        LLVM_INCLUDE_TESTS = false;
        LLVM_INCLUDE_BENCHMARKS = false;
        LLVM_COMPILER_CHECKED = true; # Skip compiler version checks
        HAVE_CXX_ATOMICS_WITHOUT_LIB = true; # Atomics work natively
        HAVE_CXX_ATOMICS64_WITHOUT_LIB = true;
        LIBCXX_ENABLE_STD_MODULES = false; # Avoid C++20 module checks
        LIBCXXABI_HAS_PTHREAD_API = true;
        LIBCXX_ENABLE_EXCEPTIONS = true;
        LIBCXXABI_ENABLE_EXCEPTIONS = true;
        LIBCXX_HAS_PTHREAD_API = true;
        LIBCXXABI_USE_LLVM_UNWINDER = false;
        LIBCXX_FORCE_LIBCXXABI = true;
        LIBCXX_ENABLE_WIDE_CHARACTERS = true;
        LIBCXX_INCLUDE_TESTS = false;
        LIBCXX_INCLUDE_BENCHMARKS = false;
        CMAKE_C_COMPILER = "${filc3}/bin/clang";
        CMAKE_CXX_COMPILER = "${filc3}/bin/clang";
        CMAKE_C_FLAGS = "-isystem ${libmojo}/include";
        CMAKE_CXX_FLAGS = "-isystem ${libmojo}/include";
      };
      meta.description = "Fil-C LLVM C++ runtimes";
    }).overrideAttrs
      (old: {
        src = sources.libcxx-src; # Uses filtered source with libcxx/libcxxabi
      });
}
