# Build compiler-rt for CRT files and builtins
#
# This builds LLVM's compiler-rt to produce:
#   - crtbegin.o / crtend.o (C runtime begin/end)
#   - libyolort.a (builtins library, renamed from libclang_rt.builtins)
#
# These are used by the yolo runtime and replace GCC's crt files.
{ pkgs }:

let
  lib = import ../lib { inherit pkgs; };
  sources = import ../lib/sources.nix { inherit pkgs; };
  inherit (lib) setupCcache;

  # CMake flags following upstream build_compiler_rt.sh
  cmakeFlags = [
    "-G Ninja"
    "-DCMAKE_BUILD_TYPE=Release"
    "-DCOMPILER_RT_BUILD_BUILTINS=ON"
    "-DCOMPILER_RT_BUILD_CRT=ON"
    "-DCOMPILER_RT_CRT_USE_EH_FRAME_REGISTRY=ON"
    "-DCOMPILER_RT_BUILD_SANITIZERS=OFF"
    "-DCOMPILER_RT_BUILD_XRAY=OFF"
    "-DCOMPILER_RT_BUILD_LIBFUZZER=OFF"
    "-DCOMPILER_RT_BUILD_PROFILE=OFF"
    "-DCOMPILER_RT_DEFAULT_TARGET_TRIPLE=x86_64-linux-gnu"
  ];

in
{
  compiler-rt = pkgs.stdenv.mkDerivation {
    pname = "filc-compiler-rt";
    version = "git";
    src = sources.compiler-rt-src;

    nativeBuildInputs = with pkgs; [
      cmake
      ninja
      python3
      ccache
    ];

    preConfigure = ''
      ${setupCcache}
      cd compiler-rt
      mkdir -p build
    '';

    configurePhase = ''
      runHook preConfigure
      cd build
      cmake ${pkgs.lib.concatStringsSep " " cmakeFlags} ..
      runHook postConfigure
    '';

    buildPhase = ''
      runHook preBuild
      ninja -j$NIX_BUILD_CORES
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      mkdir -p $out/lib

      # Copy and rename outputs following upstream's naming convention
      cp lib/linux/clang_rt.crtbegin-x86_64.o $out/lib/crtbegin.o
      cp lib/linux/clang_rt.crtend-x86_64.o $out/lib/crtend.o
      cp lib/linux/libclang_rt.builtins-x86_64.a $out/lib/libyolort.a

      runHook postInstall
    '';

    enableParallelBuilding = true;
    meta.description = "Fil-C compiler-rt (CRT files and builtins)";
  };
}

