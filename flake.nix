{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    # Use local nixpkgs fork with Fil-C integration
    # nixpkgs.url = "github:mbrock/nixpkgs-filc/filc-integration";
    nixpkgs.url = "path:/home/mbrock/nixpkgs";
    filc-src = {
      url = "path:/home/mbrock/fil-c";
      flake = false;
    };
  };

  outputs = { 
    self, nixpkgs, filc-src, ... 
  }:  let

    system = "x86_64-linux";

    # This is the base instance of nixpkgs we build everything from.
    base = import nixpkgs { inherit system; };

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
    
    # Filtered sources for different parts of the monorepo
    filc0-src = filterFilcSource "filc0" ["llvm" "clang" "cmake" "third-party"];
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
    # Uses filtered source to only include llvm/clang directories.
    filc0 = (mkFilcLLVMBuild {
      pname = "filc0";
      cmakeSource = "llvm";
      ninjaTargets = ["clang"];
      installTargets = ["install-clang" "install-clang-resource-headers"];
      cmakeOptions = {
        LLVM_ENABLE_PROJECTS = "clang";
      };
      meta.description = "Fil-C Clang compiler (LLVM stage only)";
    }).overrideAttrs (old: {
      src = filc0-src;
    });

    # Fil-C headers as separate derivations
    filc-stdfil-headers = base.runCommand "filc-stdfil-headers" {} ''
      mkdir -p $out
      cp ${libpas-src}/filc/include/*.h $out/
    '';

    # From the bare compiler, we can create the first compiler stage,
    # which adds the basic yolo runtime and headers.
    filc1 = mkFilcClang {
      crtLib = mkFilcCrtLib {};
      yoloInclude = "${libyolo-glibc}/include";
      osInclude = "${base.linuxHeaders}/include";
      stdfilInclude = filc-stdfil-headers;
    };

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
        LLVM_PATH = "../llvm";  # Point to LLVM cmake modules
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
      src = filc0-src;  # Uses same LLVM/clang source as filc0
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
      
      # Copy all .o files and static libs
      cp ${libyolo-glibc}/lib/*.o .
      cp ${libyolo-glibc}/lib/*.a .
      chmod -R u+w .
      
      # Copy and rename dynamic linker
      cp ${libyolo-glibc}/lib/ld-linux-x86-64.so.2 ld-yolo-x86_64.so
      patchelf --remove-rpath ld-yolo-x86_64.so
      
      # Copy and patch libc implementation
      cp ${libyolo-glibc}/lib/libc.so.6 libyolocimpl.so
      patchelf --set-soname libyolocimpl.so \
               --replace-needed ld-linux-x86-64.so.2 ld-yolo-x86_64.so \
               --set-rpath '$ORIGIN' \
               libyolocimpl.so
      
      # Copy and patch libm implementation  
      cp ${libyolo-glibc}/lib/libm.so.6 libyolomimpl.so
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
    libpizlo = let
      makefile = base.writeText "Makefile" ''
        CLANG_INCLUDE := $(shell ${base-clang}/bin/clang -print-resource-dir)/include
        PASCC = ${base.ccache}/bin/ccache ${base-clang}/bin/clang -march=x86-64-v2 -fPIC -pthread -nostdinc \
          -isystem ${libyolo-glibc}/include -isystem ${base.linuxHeaders}/include \
          -isystem $(CLANG_INCLUDE) -I../filc/include \
          -g -O3 -W -Werror -fno-strict-aliasing
        
        FILCC = ${filc1}/bin/clang -fPIC -O3 -g -W -Werror -I../filc/include
        
        PAS_SRCS := $(wildcard src/libpas/*.c src/mbmalloc/*.c)
        FIL_SRCS := $(wildcard ../filc/src/*.c)
        
        PAS_OBJS := $(patsubst %.c,build/%.o,$(notdir $(PAS_SRCS)))
        FIL_OBJS := $(patsubst %.c,build/filc_%.o,$(notdir $(FIL_SRCS)))
        
        all: build/libpizlo.so build/libpizlo.a build/filc_crt.o build/filc_mincrt.o
        
        build/%.o: src/libpas/%.c | build
        	$(PASCC) -c -o $@ $<
        
        build/%.o: src/mbmalloc/%.c | build
        	$(PASCC) -c -o $@ $<
        
        build/filc_%.o: ../filc/src/%.c | build
        	$(FILCC) -c -o $@ $<
        
        build/libpizlo.so: $(PAS_OBJS) $(FIL_OBJS)
        	${base-clang}/bin/clang -shared -o $@ $^ -L${libyolo}/lib -lyoloc -lyolom \
        	  $(shell ${base.gcc.cc}/bin/gcc -print-file-name=libgcc.a)
        
        build/libpizlo.a: $(PAS_OBJS) $(FIL_OBJS)
        	${base.binutils}/bin/ar cr $@ $^
        
        build/filc_crt.o: ../filc/main/main.c | build
        	$(FILCC) -c -o $@ $< -DUSE_LIBC=1
        
        build/filc_mincrt.o: ../filc/main/main.c | build
        	$(FILCC) -c -o $@ $< -DUSE_LIBC=0
        
        build:
        	mkdir -p build
      '';
    in base.stdenv.mkDerivation {
      pname = "libpizlo";
      version = "git";
      src = libpas-src;
      
      nativeBuildInputs = [base.gnumake];  # Everything else uses explicit paths
      
      buildPhase = ''
        ${setupCcache}
        cp ${makefile} libpas/Makefile
        make -C libpas -j$NIX_BUILD_CORES
      '';
      
      installPhase = ''
        mkdir -p $out/lib $out/include
        cp libpas/build/libpizlo.so $out/lib/
        cp libpas/build/libpizlo.a $out/lib/
        cp libpas/build/filc_crt.o $out/lib/
        cp libpas/build/filc_mincrt.o $out/lib/
        cp filc/include/*.h $out/include/
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
      ];

      meta.description = "Memory-safe glibc compiled with Fil-C";
    };

    # libxcrypt compiled with Fil-C
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
      ${base.ccache}/bin/ccache ${filc2}/bin/${flavor} "$@"
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
        echo "${filc-sysroot}/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
      '';
    };

    # Fil-C toolchain with full C and C++ support
    filcc = base.wrapCCWith {
      cc       = filc-cc;
      libc     = filc-sysroot;
      libcxx   = filc-libcxx;  # Prevent wrapper from adding GCC C++ headers
      bintools = filc-bintools;
      isClang  = true;

      extraBuildCommands = ''
        echo "-Wno-unused-command-line-argument" >> $out/nix-support/cc-cflags
        echo "-nostdinc++" >> $out/nix-support/libcxx-cxxflags
        echo "-isystem ${filc-libcxx}/include/c++" >> $out/nix-support/libcxx-cxxflags
        echo "-L${filc-libcxx}/lib" >> $out/nix-support/cc-ldflags
      '';    
    };

    # Some boring code follows...

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

    # Fil-C stdenv; evaluating packages from this collection
    # attempts to use Fil-C for all build tools, transitively!
    # Sometimes it even works.
    filenv = base.overrideCC base.stdenv filcc;

    # More iteratively, this wrapper just applies Fil-C to a single package,
    # and if the package has any runtime dependencies, you have to apply Fil-C to
    # those as well, using overrides.
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

    # Setup hook to patch config.sub for filc
    updateAutotoolsFilcHook = base.makeSetupHook {
      name = "update-autotools-filc-hook";
    } ./update-autotools-filc.sh;

    # Fil-C overlay: provides filcc and setup hooks to nixpkgs
    filc-overlay = final: prev: {
      inherit filcc updateAutotoolsFilcHook;
    };

    # Base nixpkgs with Fil-C overlay
    nixpkgs-with-filc = import nixpkgs {
      inherit system;
      overlays = [ filc-overlay ];
    };

    # Cross-compilation approach using pkgsCross.filc-x86_64
    filpkgs-cross = nixpkgs-with-filc.pkgsCross.filc-x86_64;

    # Native-style variant using pkgsFilC (like pkgsMusl)
    filpkgs-native = nixpkgs-with-filc.pkgsFilC;

    # Sample packages built with Fil-C
    sample-packages = import ./packages.nix {
      inherit base filenv filc-src withFilC parallelize dontTest debug;
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

  in {
    # Finally, we define the package collection!
    packages.${system} = rec {
      inherit filpkgs filpkgs-cross filpkgs-native;

      # Fil-C compiler components
      inherit filc0;
      inherit filc1;
      inherit filc2;
      inherit filc-libcxx;
      
      # Fil-C layers
      inherit libyolo-glibc;
      inherit libyolo;
      inherit libpizlo;
      inherit libmojo;
      inherit filc-xcrypt;
      inherit filc-sysroot;
      inherit filcc;
    }
    # Import sample packages
    // sample-packages
    // {
      # Also expose libxcrypt from core toolchain
      libxcrypt = filc-xcrypt;
      
      # Expose ports as a namespace
      inherit ports;
      
      # Expose combined environment
      inherit fil-c-env;
    };

    devShells.${system} = {
      # Developer shell with Fil-C compiler and tools
      default = base.mkShell {
        name = "filc-dev";
        
        buildInputs = with base; [
          filc3  # The only compiler users need
          
          # Build tools
          cmake ninja ccache git
          
          # Debug/analysis tools
          gdb valgrind strace ltrace hexdump
          
          # Useful utilities
          ripgrep fd jq bat
        ];
        
        shellHook = ''
          echo "╔════════════════════════════════════════════════════════════╗"
          echo "║          Fil-C Development Environment                     ║"
          echo "╚════════════════════════════════════════════════════════════╝"
          echo
          echo "Compiler: ${filc3}/bin/clang"
          ${filc3}/bin/clang --version | head -1
          echo
          echo "Components:"
          echo "  Runtime:   ${libpizlo.name}"
          echo "  Libc:      ${libmojo.name} (memory-safe)"
          echo "  C++ STL:   ${filc-libcxx.name}"
          echo
          echo "Quick commands:"
          echo "  clang hello.c -o hello    - Compile with Fil-C"
          echo "  clang++ test.cpp -o test  - Compile C++ with Fil-C"
          echo "  nix build .#sample-hello  - Build sample programs"
          echo
        '';
      };
      
      # Pure Fil-C environment - all tools compiled with Fil-C
      pure = base.mkShell {
        name = "filc-pure";
        
        buildInputs = with ports; [
          bash coreutils grep sed diffutils
          vim git tmux
          zlib openssl curl
          sqlite lua
        ];
        
        shellHook = ''
          echo "╔════════════════════════════════════════════════════════════╗"
          echo "║       Pure Fil-C Environment (All Tools Memory-Safe)      ║"
          echo "╚════════════════════════════════════════════════════════════╝"
          echo
          echo "All binaries in this shell were compiled with Fil-C!"
          echo
          echo "Available tools:"
          echo "  bash, coreutils (ls, cat, etc.), grep, sed, diff"
          echo "  vim, git, tmux, curl, sqlite, lua"
          echo
          echo "Try it out:"
          echo "  bash --version"
          echo "  ls -la"
          echo "  git --version"
          echo
        '';
      };
      
      # Workspace with all fil-c project sources
      workspace = let
        # Each project gets its own directory in the store
        mkProjectDir = name: src: base.runCommand "${name}-project" {} ''
          mkdir -p $out/src
          ln -s ${src} $out/src
        '';
        
        # Combine into one workspace
        workspace = base.linkFarm "filc-workspace" 
          (lib.mapAttrsToList (name: pkg: {
            name = name;
            path = mkProjectDir name (pkg.src or "${filc-src}/projects/${name}");
          }) ports);
      in base.mkShell {
        name = "filc-workspace";
        
        buildInputs = [ filc3 base.tree ];
        
        shellHook = ''
          cd ${workspace}
          
          echo "╔════════════════════════════════════════════════════════════╗"
          echo "║          Fil-C Projects Workspace                          ║"
          echo "╚════════════════════════════════════════════════════════════╝"
          echo
          echo "Workspace: ${workspace}"
          echo
          echo "Projects available (${toString (builtins.length (builtins.attrNames ports))} total):"
          ls -1 | column -c 80
          echo
          echo "Each project has a 'src/' directory with source code."
          echo
          echo "Examples:"
          echo "  cd bash/src && ls"
          echo "  cd vim/src && vim --version"
          echo "  tree -L 2 | head -20"
          echo
        '';
      };
    };
  };
}
