{ base }:

let
  lib = base.lib;
  join = lib.concatStringsSep;

  # Toolchain versions
  gcc = base.gcc14;
  llvm = base.llvmPackages_20;
  llvmMajor = lib.versions.major llvm.release_version;
  targetPlatform = base.stdenv.targetPlatform.config;
  gcc-lib = "${gcc.cc}/lib/gcc/${targetPlatform}/${gcc.version}";

  # Standard ccache setup for all builds
  setupCcache = ''
    if [ -w "/nix/var/cache/ccache" ]; then
      export CCACHE_DIR=/nix/var/cache/ccache
      export CCACHE_COMPRESS=1
      export CCACHE_SLOPPINESS=random_seed
      export CCACHE_UMASK=007
    else
      export CCACHE_DISABLE=1
    fi
  '';

  commonLLVMOptions = {
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
  };

  # Convert attribute set to CMake flags
  cmakeFlags = opts: lib.mapAttrsToList (k: v:
    let val = if lib.isBool v then (if v then "ON" else "OFF") else toString v;
    in "-D${k}=${val}"
  ) opts;

  # This is just a function that abstracts some common stuff
  # for doing CMake/ninja/ccache builds.
  mkFilcLLVMBuild = {
    pname,
    cmakeOptions ? {},
    cmakeSource,
    buildDir ? "build",
    ninjaTargets ? [],
    installTargets ? ["install"],
    preConfigure ? "",
    postBuild ? "",
    customInstall ? null,
    meta ? {}
  }:
    base.ccacheStdenv.mkDerivation {
      inherit pname meta;
      version = "git";

      # Let Nix decide how many cores to use.
      enableParallelBuilding = true;

      nativeBuildInputs = with base; [
        cmake ninja python3 git patchelf ccache lld
      ];

      configurePhase = let
        allOptions = commonLLVMOptions // cmakeOptions;
      in ''
        export HOME=$TMPDIR
        export HOSTNAME=nix-build
        ${setupCcache}

        ${preConfigure}

        mkdir -p ${buildDir}
        cmake -B ${buildDir} -S ${cmakeSource} -G Ninja ${join " " (cmakeFlags allOptions)}
      '';

      buildPhase = ''
        NINJA_STATUS="[B %f/%t %es] " ninja -v -C ${buildDir} ${join " " ninjaTargets}
        ${postBuild}
      '';

      installPhase = if customInstall != null then customInstall else ''
        NINJA_STATUS="[I %f/%t %es] " ninja -v -C ${buildDir} ${join " " installTargets}
      '';
    };

  # Merge multiple derivations into one (layers applied in order)
  mergeLayers = name: layers: base.runCommand name {
    nativeBuildInputs = [base.rsync];
  } ''
    mkdir -p $out/{lib,include,bin}
    ${lib.concatMapStringsSep "\n" (layer: ''
      [ -d ${layer}/lib ] && rsync -a ${layer}/lib/ $out/lib/ || true
      [ -d ${layer}/include ] && rsync -a ${layer}/include/ $out/include/ || true
      [ -d ${layer}/bin ] && rsync -a ${layer}/bin/ $out/bin/ || true
    '') layers}
    chmod -R u+w $out
  '';

  # Add nixpkgs libc contract metadata to a sysroot
  addLibcMetadata = sysroot: { dynamicLinker, crts ? ["crt1.o" "crti.o" "crtn.o"] }:
    base.runCommand "${sysroot.name}-with-metadata" {} ''
      cp -r ${sysroot} $out
      chmod -R u+w $out
      mkdir -p $out/nix-support
      echo "$out/lib/${dynamicLinker}" > $out/nix-support/dynamic-linker
      ${lib.concatMapStringsSep "\n" (crt: ''
        [ -f "$out/lib/${crt}" ] && echo "$out/lib/${crt}" > "$out/nix-support/${crt}"
      '') crts}
    '';

in {
  inherit lib join;
  inherit gcc llvm llvmMajor targetPlatform gcc-lib;
  inherit setupCcache commonLLVMOptions cmakeFlags;
  inherit mkFilcLLVMBuild mergeLayers addLibcMetadata;

  # Define a version of the host Clang that doesn't have any
  # automatic stuff, to build libpizlo in a clean and consistent way.
  clang-rsrc = base.lib.getLib llvm.clang.cc;
  clang-include = "${base.lib.getLib llvm.clang.cc}/lib/clang/${llvmMajor}/include";
  base-clang = base.writeShellScriptBin "clang" ''
    exec ${llvm.clang.cc}/bin/clang -isystem ${base.lib.getLib llvm.clang.cc}/lib/clang/${llvmMajor}/include "$@"
  '';
}
