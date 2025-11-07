{
  pkgs,
}:

let
  lib = import ../lib { inherit pkgs; };
  sources = import ../lib/sources.nix { inherit pkgs; };

  inherit (lib) setupCcache;
  stdlib = pkgs.lib;

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
  filc0 = pkgs.ccacheStdenv.mkDerivation {
    pname = "filc0";
    version = "git";
    src = sources.filc0-src;

    outputs = [
      "out"
      "dev"
      "bin"
      "lib"
    ];

    patches = [ ./filc0-symver.patch ];

    enableParallelBuilding = true;

    nativeBuildInputs = with pkgs; [
      cmake
      ninja
      python3
      git
      patchelf
      ccache
      binutils
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
          CMAKE_INSTALL_PREFIX = "$TMPDIR/install";
          LLVM_USE_LINKER = "gold";
          LLVM_ENABLE_PROJECTS = "clang";
          LLVM_BINUTILS_INCDIR = "${pkgs.binutils-unwrapped.dev}/include";
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
      # Install everything to a temporary location
      NINJA_STATUS="[I %f/%t %es] " ninja -v -C build install

      cd $TMPDIR/install

      # --- OUTPUT: out (essential compiler toolchain) ---
      mkdir -p $out/bin

      # Core compiler binary (clang is the real binary, others are symlinks)
      cp -p bin/clang $out/bin/clang

      # Create symlinks for clang variants (they share the same binary)
      for tool in clang++ clang-20 clang-cl clang-cpp; do
        if [ -e "bin/$tool" ]; then
          ln -s clang $out/bin/$tool
        fi
      done

      # Essential LLVM binary utilities (equivalent to GNU binutils)
      # Note: Some of these are hard links to the same binary

      # llvm-ar is the main binary, llvm-ranlib links to it
      [ -e bin/llvm-ar ] && cp -p bin/llvm-ar $out/bin/
      [ -e bin/llvm-ranlib ] && ln -s llvm-ar $out/bin/llvm-ranlib

      # llvm-objcopy is the main binary, llvm-strip links to it
      [ -e bin/llvm-objcopy ] && cp -p bin/llvm-objcopy $out/bin/
      [ -e bin/llvm-strip ] && ln -s llvm-objcopy $out/bin/llvm-strip

      # llvm-readobj is the main binary, llvm-readelf links to it
      [ -e bin/llvm-readobj ] && cp -p bin/llvm-readobj $out/bin/
      [ -e bin/llvm-readelf ] && ln -s llvm-readobj $out/bin/llvm-readelf

      # These are typically standalone binaries
      for tool in llvm-nm llvm-objdump llvm-size llvm-strings llvm-addr2line; do
        [ -e "bin/$tool" ] && cp -p "bin/$tool" $out/bin/
      done

      # LLVM core tools for compilation pipeline
      for tool in \
        llvm-as llvm-dis \
        llvm-link \
        opt llc lli \
        llvm-config; do
        [ -e "bin/$tool" ] && cp -p "bin/$tool" $out/bin/
      done

      # Linker (lld is main binary, variants are symlinks)
      [ -e bin/lld ] && cp -p bin/lld $out/bin/
      for tool in ld.lld ld64.lld wasm-ld; do
        [ -e "bin/$tool" ] && ln -s lld $out/bin/$tool
      done

      # LTO-related tools
      for tool in llvm-lto llvm-lto2; do
        [ -e "bin/$tool" ] && cp -p "bin/$tool" $out/bin/
      done

      # Clang driver wrappers and resource tools
      for tool in \
        clang-linker-wrapper \
        clang-offload-bundler clang-offload-packager; do
        [ -e "bin/$tool" ] && cp -p "bin/$tool" $out/bin/
      done

      # Clang resource directory (headers, libs for compilation)
      mkdir -p $out/lib
      if [ -d lib/clang ]; then
        cp -r lib/clang $out/lib/
      fi

      # LTO gold plugin (essential for LTO with ld.gold)
      if [ -e lib/LLVMgold.so ]; then
        cp -p lib/LLVMgold.so $out/lib/
      fi

      # Shared libraries needed at runtime (copy all symlinks and files)
      if ls lib/libclang.so* 1> /dev/null 2>&1; then
        cp -a lib/libclang.so* $out/lib/
      fi
      if ls lib/libclang-cpp.so* 1> /dev/null 2>&1; then
        cp -a lib/libclang-cpp.so* $out/lib/
      fi
      if ls lib/libLTO.so* 1> /dev/null 2>&1; then
        cp -a lib/libLTO.so* $out/lib/
      fi
      if ls lib/libRemarks.so* 1> /dev/null 2>&1; then
        cp -a lib/libRemarks.so* $out/lib/
      fi

      # --- OUTPUT: dev (headers + static libs for LLVM development) ---
      mkdir -p $dev/include
      cp -r include/* $dev/include/

      mkdir -p $dev/lib
      cp -p lib/*.a $dev/lib/ 2>/dev/null || true

      # CMake files for find_package(LLVM) and find_package(Clang)
      [ -d lib/cmake ] && cp -r lib/cmake $dev/lib/

      # --- OUTPUT: bin (extra LLVM tools and utilities) ---
      mkdir -p $bin/bin
      for tool in bin/*; do
        toolname=$(basename "$tool")
        # Skip if already in $out
        [ ! -e "$out/bin/$toolname" ] && cp -p "$tool" $bin/bin/
      done

      # --- OUTPUT: lib (documentation, helper scripts, misc) ---
      [ -d libexec ] && mkdir -p $lib/libexec && cp -r libexec/* $lib/libexec/
      [ -d share ] && mkdir -p $lib/share && cp -r share/* $lib/share/
    '';

    meta = {
      description = "Fil-C Clang compiler (LLVM stage only, pinned and isolated)";
      outputsToInstall = [ "out" ];
    };
  };
}
