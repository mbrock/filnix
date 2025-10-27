{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    nixpkgs.url =
      "github:NixOS/nixpkgs/c8aa8cc00a5cb57fada0851a038d35c08a36a2bb";
    # nixos-generators = {
    #   url = "github:nix-community/nixos-generators";
    #   inputs.nixpkgs.follows = "nixpkgs";
    # };
  };

  outputs = { self, nixpkgs, ... }:  let
    system = "x86_64-linux";
    base = import nixpkgs { inherit system; };

    filc-src = filc0-src;
    filc0-src = base.fetchgit {
      url = "https://github.com/mbrock/fil-c";
      rev = "83a0ae7ee07dd09050cc9c331d6ae88d513d0248";
      hash = "sha256-/yhpZSGYhWdQ7+bux3cPcBwmv5i01SFuH+ST30vwhaI=";
    };

    kitty-doom-src = base.fetchgit {
      url = "https://github.com/mbrock/kitty-doom";
      rev = "ca6c5e40156617489712746bbb594e66293a0aa1";
      hash = "sha256-2DRLohKapV0TiF0ysxITv8yaIprLbV4BU/f6o6IwX40=";
    };

    doom1-wad = base.fetchurl {
      url = "https://distro.ibiblio.org/slitaz/sources/packages/d/doom1.wad";
      hash = "sha256-0wf7r8kaalpn2qc74ng8flqg6fwwwbrviq0mwhkxjrqya2z46z8x";
    };

    puredoom-h = base.fetchurl {
      url = "https://raw.githubusercontent.com/Daivuk/PureDOOM/master/PureDOOM.h";
      hash = "sha256-0rypvk8m90qvir13jiwxw7jklszawsvz3g7h2g5if4361mqghbbg";
    };

    wasm3-src = base.fetchgit {
      url = "https://github.com/wasm3/wasm3";
      rev = "79d412ea5fcf92f0efe658d52827a0e0a96ff442";
      hash = "sha256-CmNngYLD/PtiEW8pGORjW4d7TAmW5ZZMBAeKzJYMMdw=";
    };

    lib = base.lib;
    join = lib.concatStringsSep;

    # Toolchain versions
    gcc = base.gcc14;
    llvm = base.llvmPackages_20;
    llvmMajor = lib.versions.major llvm.release_version;
    targetPlatform = base.stdenv.targetPlatform.config;
    gcc-lib = "${gcc.cc}/lib/gcc/${targetPlatform}/${gcc.version}";

    # Filtered source paths to reduce disk usage and improve caching
    # Helper to filter monorepo to only include specific top-level directories
    filterFilcSource = name: dirs: builtins.path {
      path = filc-src;
      name = "${name}-source";
      filter = path: type:
        let
          relPath = lib.removePrefix (toString filc-src + "/") (toString path);
          topDir = builtins.head (lib.splitString "/" relPath);
        in
        builtins.elem topDir dirs;
    };
    
    # Maximally filtered source for filc0 - only what's needed for clang build
    filc0-src-filtered = builtins.path {
      path = filc0-src;
      name = "filc0-source";
      filter = path: type:
        let
          relPath = lib.removePrefix (toString filc0-src + "/") (toString path);
          topDir = builtins.head (lib.splitString "/" relPath);
        in
        builtins.elem topDir ["llvm" "clang" "cmake" "third-party"];
    };

    # Filtered sources for different parts of the monorepo
    libcxx-src = filterFilcSource "libcxx" ["llvm" "clang" "cmake" "third-party" "libcxx" "libc" "libcxxabi" "runtimes"];
    libpas-src = filterFilcSource "libpas" ["libpas" "filc"];
    filc-projects-src = filterFilcSource "filc-projects" ["projects"];

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
        src = filc-src;

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

    # This is the basic Fil-C Clang LLVM build.
    # It produces a bare compiler without Fil-C runtime.
    # Uses pinned source and inlined build logic to avoid casual rebuilds.
    filc0 = base.ccacheStdenv.mkDerivation {
      pname = "filc0";
      version = "git";
      src = filc0-src-filtered;

      enableParallelBuilding = true;

      nativeBuildInputs = with base; [
        cmake ninja python3 git patchelf ccache lld
      ];

      configurePhase = let
        cmakeFlags = lib.mapAttrsToList (k: v:
          let val = if lib.isBool v then (if v then "ON" else "OFF") else toString v;
          in "-D${k}=${val}"
        );
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
      in ''
        export HOME=$TMPDIR
        export HOSTNAME=nix-build
        export CCACHE_COMPRESS=1
        export CCACHE_SLOPPINESS=random_seed
        export CCACHE_DIR="/nix/var/cache/ccache"
        export CCACHE_UMASK=007

        mkdir -p build
        cmake -B build -S llvm -G Ninja ${lib.concatStringsSep " " (cmakeFlags allOptions)}
      '';

      buildPhase = ''
        NINJA_STATUS="[B %f/%t %es] " ninja -v -C build clang
      '';

      installPhase = ''
        NINJA_STATUS="[I %f/%t %es] " ninja -v -C build install-clang install-clang-resource-headers
      '';

      meta.description = "Fil-C Clang compiler (LLVM stage only, pinned and isolated)";
    };

    # Fil-C headers as separate derivations
    filc-stdfil-headers = base.runCommand "filc-stdfil-headers" {} ''
      mkdir -p $out
      cp ${libpas-src}/filc/include/*.h $out/
    '';

    # From the bare compiler, we can create the first compiler stage,
    # which adds the basic yolo runtime and headers.
    # Keep it minimal - just the compiler, no extra wrapper flags
    filc1 = base.runCommand "filc1" {
      nativeBuildInputs = [base.makeWrapper];
    } ''
      mkdir -p $out/bin
      makeWrapper ${filc0}/bin/clang $out/bin/clang \
        --add-flags "--gcc-toolchain=${gcc.cc}" \
        --add-flags "-resource-dir ${filc0}/lib/clang/${llvmMajor}"
      ln -s clang $out/bin/clang++
    '';

    # Second compiler stage adds the Fil-C runtime, compiled using filc1.
    filc2 = mkFilcClang {
      crtLib = mkFilcCrtLib { filcRuntimeLibs = libpizlo; };
      yoloInclude = "${libyolo-glibc}/include";
      osInclude = "${base.linuxHeaders}/include";
      stdfilInclude = filc-stdfil-headers;
    };

    # Third compiler stage uses memory-safe glibc (libmojo)
    # We keep this as a simple wrapper since it just adds libmojo on top of filc2
    filc3 = base.runCommand "filc3" {
      nativeBuildInputs = [base.makeWrapper];
    } ''
      mkdir -p $out/bin
      makeWrapper ${filc2}/bin/clang $out/bin/clang \
        --add-flags "-isystem ${libmojo}/include" \
        --add-flags "-L${libmojo}/lib"
      ln -s clang $out/bin/clang++
    '';

    # Then we use filc3 to build libcxx!
    filc-libcxx = (mkFilcLLVMBuild {
      pname = "filc-libcxx";
      preConfigure = "";
      cmakeSource = "runtimes";
      buildDir = "build";
      ninjaTargets = [];
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
        LLVM_COMPILER_CHECKED = true;  # Skip compiler version checks
        HAVE_CXX_ATOMICS_WITHOUT_LIB = true;  # Atomics work natively
        HAVE_CXX_ATOMICS64_WITHOUT_LIB = true;
        LIBCXX_ENABLE_STD_MODULES = false;  # Avoid C++20 module checks
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
    }).overrideAttrs (old: {
      src = libcxx-src;  # Uses filtered source with libcxx/libcxxabi
    });

    # Build CRT library directory (libyolo + gcc crt files + optional filc runtime)
    mkFilcCrtLib = { filcRuntimeLibs ? null }: base.runCommand "filc-crt-lib" {
      nativeBuildInputs = [base.rsync];
    } ''
      mkdir -p $out
      
      # Libraries: yolo + gcc crt files + optional filc runtime
      rsync -a ${libyolo}/lib/ $out/
      chmod -R u+w $out
      cp ${gcc-lib}/crt*.o $out/
      cp ${gcc-lib}/libgcc* $out/ || true
      mkdir -p $out/gcc/${targetPlatform}/${gcc.version}
      cp -r ${gcc-lib}/* $out/gcc/${targetPlatform}/${gcc.version}/
      
      ${lib.optionalString (filcRuntimeLibs != null) ''
        cp ${filcRuntimeLibs}/lib/filc_crt.o $out/ || true
        cp ${filcRuntimeLibs}/lib/filc_mincrt.o $out/ || true
        cp ${filcRuntimeLibs}/lib/libpizlo.so $out/ || true
        cp ${filcRuntimeLibs}/lib/libpizlo.a $out/ || true
      ''}
    '';

    # Assemble Fil-C compiler with explicit flags instead of pizfix directory layout
    mkFilcClang = { crtLib, yoloInclude, osInclude, stdfilInclude }: base.runCommand "filc" {
      nativeBuildInputs = [base.makeWrapper];
    } ''
      mkdir -p $out/bin
      
      # Wrap clang with Fil-C paths using explicit flags
      makeWrapper ${filc0}/bin/clang-${llvmMajor} $out/bin/clang \
        --add-flags -v \
        --add-flags "--gcc-toolchain=${gcc.cc}" \
        --add-flags "-resource-dir ${filc0}/lib/clang/${llvmMajor}" \
        --add-flags "--filc-dynamic-linker=${crtLib}/ld-yolo-x86_64.so" \
        --add-flags "--filc-crt-path=${crtLib}" \
        --add-flags "--filc-stdfil-include=${stdfilInclude}" \
        --add-flags "--filc-os-include=${osInclude}" \
        --add-flags "--filc-include=${yoloInclude}"
      
      ln -s clang $out/bin/clang++
    '';
   
    # This just builds the Fil-C glibc yolo fork with the normal
    # host GCC toolchain.
    libyolo-glibc = base.stdenv.mkDerivation rec {
      pname = "libyolo-glibc";
      version = "2.40";
      src = "${filc-src}/projects/yolo-glibc-${version}";
      
      # Use single output (glibc tries to split into multiple outputs by default)
      outputs = ["out"];
      
      enableParallelBuilding = true;

      nativeBuildInputs = with base; [
        python3 git file patchelf gnumake pkg-config autoconf bison
        gcc-unwrapped binutils-unwrapped ccache
      ];

      preConfigure = ''
        export NIX_CFLAGS_COMPILE=""
        export NIX_LDFLAGS=""
        
        # Set up ccache manually
        ${setupCcache}
        export CC="ccache gcc"
        export CXX="ccache g++"
        
        # glibc requires out-of-tree build
        autoconf
        cd ..
        mkdir -p build
        cd build
        configureScript=$PWD/../$sourceRoot/configure
        
        # Set these in shell so $out actually expands
        configureFlagsArray+=(
          "libc_cv_slibdir=$out/lib"
        )
      '';

      configureFlags = [
        "--disable-mathvec"
        "--disable-nscd"
        "--disable-werror"
        "--with-headers=${base.linuxHeaders}/include"
      ];
    };

    # Rename yolo-glibc components so they don't conflict with normal glibc
    libyolo = base.runCommand "libyolo" {
      nativeBuildInputs = [base.patchelf];
    } ''
      mkdir -p $out/lib
      cd $out/lib
      
      # Copy all .o files
      cp ${libyolo-glibc}/lib/*.o .
      
      # Copy and rename static libs
      cp ${libyolo-glibc}/lib/libc.a libyoloc.a
      cp ${libyolo-glibc}/lib/libc_nonshared.a libyoloc_nonshared.a
      cp ${libyolo-glibc}/lib/libm.a libyolom.a
      cp ${libyolo-glibc}/lib/*.a .  # Copy other .a files as-is
      chmod -R u+w .
      
      # Copy and rename dynamic linker
      cp ${libyolo-glibc}/lib/ld-linux-x86-64.so.2 ld-yolo-x86_64.so
      chmod u+w ld-yolo-x86_64.so
      patchelf --remove-rpath ld-yolo-x86_64.so
      
      # Copy and patch libc implementation
      cp ${libyolo-glibc}/lib/libc.so.6 libyolocimpl.so
      chmod u+w libyolocimpl.so
      patchelf --set-soname libyolocimpl.so \
               --replace-needed ld-linux-x86-64.so.2 ld-yolo-x86_64.so \
               --set-rpath '$ORIGIN' \
               libyolocimpl.so
      
      # Copy and patch libm implementation  
      cp ${libyolo-glibc}/lib/libm.so.6 libyolomimpl.so
      chmod u+w libyolomimpl.so
      patchelf --set-soname libyolomimpl.so \
               --replace-needed ld-linux-x86-64.so.2 ld-yolo-x86_64.so \
               --replace-needed libc.so.6 libyolocimpl.so \
               --set-rpath '$ORIGIN' \
               libyolomimpl.so
      
      # Create linker scripts
      cat > libyolom.so <<'EOF'
      OUTPUT_FORMAT(elf64-x86-64)
      GROUP(libyolomimpl.so)
      EOF
      
      cat > libyoloc.so <<'EOF'
      OUTPUT_FORMAT(elf64-x86-64)
      GROUP(libyolocimpl.so libyoloc_nonshared.a AS_NEEDED(ld-yolo-x86_64.so))
      EOF
    '';

    # Define a version of the host Clang that doesn't have any
    # automatic stuff, to build libpizlo in a clean and consistent
    # way.
    clang-rsrc = base.lib.getLib llvm.clang.cc;
    clang-include = "${clang-rsrc}/lib/clang/${llvmMajor}/include";
    base-clang = base.writeShellScriptBin "clang" ''
      exec ${llvm.clang.cc}/bin/clang -isystem ${clang-include} "$@"
    '';

    # Build libpizlo (Fil-C runtime library - GC + memory safety)
    # Use the original Makefile - it knows which files to build
    libpizlo = base.stdenv.mkDerivation {
      pname = "libpizlo";
      version = "git";
      src = libpas-src;
      
      nativeBuildInputs = [base.gnumake base.ruby base-clang filc1 base.ccache];
      
      sourceRoot = "libpas-source/libpas";
      
      postUnpack = ''
        chmod -R u+w libpas-source
        
        # Makefile expects ../pizfix structure with multiple lib variants and renamed libyolo libs
        mkdir -p libpas-source/pizfix/{lib,lib_test,lib_gcverify,lib_test_gcverify,yolo-include,os-include,stdfil-include}
        cp ${libyolo}/lib/*.{so,a,o} libpas-source/pizfix/lib/ 2>/dev/null || true
        cp ${libyolo-glibc}/include/* libpas-source/pizfix/yolo-include/ -r
        cp ${base.linuxHeaders}/include/* libpas-source/pizfix/os-include/ -r
        
        # Makefile expects ../build/bin/clang
        mkdir -p libpas-source/build/bin
        ln -s ${filc1}/bin/clang libpas-source/build/bin/clang
      '';
      
      preConfigure = ''
        ${setupCcache}
        export CC="ccache clang"
        patchShebangs .
      '';
      
      buildPhase = ''
        mkdir -p build
        ${base.ruby}/bin/ruby src/libpas/generate_pizlonated_forwarders.rb src/libpas/filc_native.h
        make -j$NIX_BUILD_CORES FILCFLAGS="-O3 -g -W -Werror -MD -I../filc/include"
      '';
      
      installPhase = ''
        mkdir -p $out/lib $out/include
        cp ../pizfix/lib/libpizlo.so $out/lib/
        cp ../pizfix/lib/libpizlo.a $out/lib/
        cp ../pizfix/lib/filc_crt.o $out/lib/
        cp ../pizfix/lib/filc_mincrt.o $out/lib/
        cp ../filc/include/*.h $out/include/
      '';

      enableParallelBuilding = true;
      meta.description = "Fil-C runtime library (libpizlo)";
    };

    # Memory-safe glibc compiled with Fil-C
    libmojo = base.stdenv.mkDerivation {
      pname = "libmojo";
      version = "2.40";
      src = "${filc-src}/projects/user-glibc-2.40";
      outputs = ["out"];
      
      enableParallelBuilding = true;

      nativeBuildInputs = with base; [
        gnumake autoconf bison python3 binutils glibc.dev
      ];

      preConfigure = ''
        # Fil-C compiler flags from build script
        FILCXXFLAGS="-nostdlibinc -Wno-ignored-attributes -Wno-pointer-sign"
        FILCFLAGS="$FILCXXFLAGS -Wno-unused-command-line-argument -Wno-macro-redefined"
        
        export CC="${filc2}/bin/clang $FILCFLAGS -isystem ${libpizlo}/include"
        export CXX="${filc2}/bin/clang++ $FILCXXFLAGS -isystem ${libpizlo}/include"
        
        # glibc requires out-of-tree build
        autoconf
        cd ..
        mkdir -p build
        cd build
        configureScript=$PWD/../$sourceRoot/configure
        
        # Set these in shell so $out actually expands
        configureFlagsArray+=(
          "libc_cv_slibdir=$out/lib"
        )
      '';

      configureFlags = [
        "--disable-mathvec"
        "--disable-nscd"
        "--disable-werror"
        "--with-headers=${base.linuxHeaders}/include"
      ];

      meta.description = "Memory-safe glibc compiled with Fil-C";
    };

    filc-xcrypt = base.stdenv.mkDerivation {
      pname = "filc-xcrypt";
      version = "4.4.36";
      src = "${filc-src}/projects/libxcrypt-4.4.36";
      enableParallelBuilding = true;

      nativeBuildInputs = with base; [
        gnumake automake116x autoconf libtool binutils perl python3
      ];

      preConfigure = ''
        export CC="${filc2}/bin/clang -isystem ${libpizlo}/include -L${libmojo}/lib -I${libmojo}/include"
        
        rm -f aclocal.m4
        libtoolize --copy --force
        autoreconf -vfi -I build-aux/m4
      '';

      meta.description = "libxcrypt compiled with Fil-C";
    };

    filc-cc = base.runCommand "filc-cc" {} ''
      mkdir -p $out/bin
      ln -s ${filcache "clang"}/bin/ccache-clang $out/bin/clang
      ln -s ${filcache "clang"}/bin/ccache-clang $out/bin/gcc
      ln -s ${filcache "clang++"}/bin/ccache-clang++ $out/bin/clang++
      ln -s ${filcache "clang++"}/bin/ccache-clang++ $out/bin/g++
    '';

    filcache = flavor: base.writeShellScriptBin ("ccache-${flavor}") ''
      ${setupCcache}
      ${base.ccache}/bin/ccache ${filc3}/bin/${flavor} "$@"
    '';

    # Complete Fil-C sysroot - the full memory-safe sandwich + C++
    filc-sysroot = addLibcMetadata
      (mergeLayers "filc-sysroot" [
        libyolo       # Layer 1: Yolo runtime libraries (bottom)
        libpizlo      # Layer 2: Memory safety runtime (middle)
        libmojo       # Layer 3: Memory-safe user glibc
        filc-libcxx   # Layer 4: C++ standard library (top)
      ])
      {
        dynamicLinker = "ld-yolo-x86_64.so";
        crts = ["crt1.o" "rcrt1.o" "Scrt1.o" "crti.o" "crtn.o"];
      };

    # Define a Nix conventional binary toolchain.
    filc-bintools = base.wrapBintoolsWith {
      bintools = base.binutils-unwrapped;
      libc     = filc-sysroot;

      extraBuildCommands = ''
        echo "-L${libmojo}/lib" >> $out/nix-support/libc-ldflags
        echo "-lpizlo -lyoloc -lyolom -lc++ -lc++abi" >> $out/nix-support/libc-ldflags
        echo "${filc-sysroot}/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
      '';
    };

    # Fil-C toolchain with full C and C++ support
    filcc = base.wrapCCWith {
      cc       = filc-cc;
      libc     = filc-sysroot;
      libcxx   = filc-libcxx;
      bintools = filc-bintools;
      isClang  = true;

      extraBuildCommands = ''
        echo "-Wno-unused-command-line-argument" >> $out/nix-support/cc-cflags
        echo "-nostdinc++" >> $out/nix-support/libcxx-cxxflags
        echo "-isystem ${filc-libcxx}/include/c++" >> $out/nix-support/libcxx-cxxflags
        echo "-L${filc-libcxx}/lib" >> $out/nix-support/cc-ldflags
      '';    
    };

    cmakeFlags = opts: lib.mapAttrsToList (k: v:
      let val = if lib.isBool v then (if v then "ON" else "OFF") else toString v;
      in "-D${k}=${val}"
    ) opts;

    # Standard ccache setup for all builds
    setupCcache = ''
      export CCACHE_COMPRESS=1
      export CCACHE_SLOPPINESS=random_seed
      export CCACHE_DIR="/nix/var/cache/ccache"
      export CCACHE_UMASK=007
    '';

    # Merge multiple derivations into one(layers applied in order)
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

    filenv = base.overrideCC base.stdenv filcc;
    withFilC = pkg: pkg.override { stdenv = filenv; };

    parallelize = pkg: pkg.overrideAttrs (_: {
      enableParallelBuilding = true;
    });

    dontTest = pkg: pkg.overrideAttrs (old: {
      doCheck = false;
    });

    debug = pkg: pkg.overrideAttrs (old: {
      nativeBuildInputs = old.nativeBuildInputs or [] ++ [base.pkgs.breakpointHook];
    });

    # experimental full Fil-C nixpkgs (original approach)
    filpkgs = import nixpkgs {
      inherit system;
      config.replaceStdenv = { pkgs, ... }:
        pkgs.overrideCC pkgs.stdenv filcc;
    };

    # Sample packages built with Fil-C
    sample-packages = import ./packages.nix {
      inherit base filenv filc-src withFilC parallelize dontTest debug;
      inherit kitty-doom-src doom1-wad puredoom-h;
      inherit wasm3-src;
    };

    # Ports: packages built directly from fil-c/projects vendored sources
    ports = import ./fil-c-projects.nix {
      inherit base filenv filc-src filcc;
    };

    # Combined: all ports merged into single output
    fil-c-env = import ./fil-c-combined.nix {
      inherit base filenv;
      packages = ports;
    };
    
    # CVE test payloads for wasm3
    wasm3-cve-payloads = (import ./wasm3-cves.nix { pkgs = base; }).cve-tests;

    # # Minimal NixOS configuration for QEMU
    # nixosConfig = {
    #   boot.loader.grub.device = "/dev/vda";
    #   boot.kernelParams = [ "console=ttyS0" ];
      
    #   users.users.root.initialPassword = "root";
    #   environment.systemPackages = [ filcc sample-packages.wasm3 ];
    #   services.getty.autologinUser = "root";
    #   documentation.enable = false;
    #   system.stateVersion = "25.05";
      
    #   system.activationScripts.setupWasm3Cves = ''
    #     mkdir -p /root/wasm3-cves
    #     cp -f ${wasm3-cve-payloads}/* /root/wasm3-cves/
    #     chmod -R u+w /root/wasm3-cves
    #   '';
    # };

  in {
    # Finally, we define the package collection!
    packages.${system} = rec {
      inherit filpkgs;
      inherit filc0;
      inherit filc1;
      inherit filc2;
      inherit filc-libcxx;
      inherit libyolo-glibc;
      inherit libyolo;
      inherit libpizlo;
      inherit libmojo;
      inherit filc-xcrypt;
      inherit filc-sysroot;
      inherit filcc;
      inherit fil-c-env;
      inherit ports;
      
      # qemu-image = nixos-generators.nixosGenerate {
      #   inherit system;
      #   format = "qcow";
      #   modules = [ nixosConfig ];
      # };
    }

    // sample-packages
    ;

    devShells.${system} = {
      default = base.mkShell {
        name = "filc-dev";
        
        buildInputs = with base; [
          filcc
          cmake ninja ccache git
          gdb valgrind strace ltrace hexdump
          ripgrep fd jq bat
        ];
        
        shellHook = ''
          clang --version | head -1
          echo
          echo "  clang    $(which clang)"
          echo "  pizlo    ${libpizlo}"
          echo "  glibc    ${libmojo}"
          echo "  libc++   ${filc-libcxx}"
          echo
        '';
      };
      
      # Pure Fil-C environment - all tools compiled with Fil-C.
      # Not currently building! Would be nice though!
      pure = base.mkShell {
        name = "filc-pure";
        
        buildInputs = with ports; [
          bash coreutils grep sed diffutils
          vim git tmux
          zlib openssl curl
          sqlite lua
        ];
      };
      
      # wasm3 CVE testing environment
      wasm3-cve-test = base.mkShell {
        name = "wasm3-cve-test";
        
        buildInputs = [ sample-packages.wasm3 ];
        
        shellHook = ''
          cd ${wasm3-cve-payloads}
          
          # Multi-line prompt to handle long store paths
          export PS1='\n\[\033[1;34m\]wasm3-cve-test\[\033[0m\] \w\n\$ '
          
          echo "Fil-C wasm3:"
          echo "  $(which wasm3)"
          echo "Test directory:"
          echo "  $PWD"
          echo
          echo "Test files:"
          ls -1 *.wasm | sed 's/^/  /'
          echo
          echo "Try running:"
          echo "  wasm3 cve-2022-39974.wasm"
          echo "  wasm3 cve-2022-34529.wasm"
          echo
          echo "See README.txt for details"
          echo
        '';
      };
    };
  };
}
