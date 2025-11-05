{
  base,
  lib,
  sources,
}:

let
  inherit (lib) setupCcache;
  stdlib = base.lib;

  cmakeFlags =
    lib.cmakeFlags or (
      opts:
      stdlib.mapAttrsToList (
        k: v:
        let
          val = if stdlib.isBool v then (if v then "ON" else "OFF") else toString v;
        in
        "-D${k}=${val}"
      ) opts
    );

in
{
  # This is the basic Fil-C Clang LLVM build.
  # It produces a bare compiler without Fil-C runtime.
  # Uses pinned source and inlined build logic to avoid casual rebuilds.
  filc0 = base.ccacheStdenv.mkDerivation {
    pname = "filc0";
    version = "git";
    src = sources.filc0-src;

    enableParallelBuilding = true;

    nativeBuildInputs = with base; [
      cmake
      ninja
      python3
      git
      patchelf
      ccache
      lld
    ];

    configurePhase =
      let
        allOptions = {
          CMAKE_BUILD_TYPE = "RelWithDebInfo";
          LLVM_ENABLE_ASSERTIONS = true;
          LLVM_ENABLE_WARNINGS = false;
          LLVM_ENABLE_ZSTD = false;
          LLVM_TARGETS_TO_BUILD = "X86";
          LLVM_ENABLE_LIBXML2 = false;
          LLVM_ENABLE_LIBEDIT = false;
          LLVM_ENABLE_LIBPFM = false;
          LLVM_ENABLE_ZLIB = false;
          LLVM_ENABLE_CURL = false;
          LLVM_ENABLE_HTTPLIB = false;
          LLVM_STATIC_LINK_CXX_STDLIB = true;
          CMAKE_EXE_LINKER_FLAGS = "-static-libgcc";
          CMAKE_INSTALL_PREFIX = "$out";
          LLVM_USE_LINKER = "lld";
          LLVM_ENABLE_PROJECTS = "clang";
        };
      in
      ''
        export HOME=$TMPDIR
        export HOSTNAME=nix-build
        ${setupCcache}

        mkdir -p build
        cmake -B build -S llvm -G Ninja ${stdlib.concatStringsSep " " (cmakeFlags allOptions)}
      '';

    buildPhase = ''
      NINJA_STATUS="[B %f/%t %es] " ninja -v -C build clang
    '';

    installPhase = ''
      NINJA_STATUS="[I %f/%t %es] " ninja -v -C build install-clang install-clang-resource-headers
    '';

    meta.description = "Fil-C Clang compiler (LLVM stage only, pinned and isolated)";
  };
}
