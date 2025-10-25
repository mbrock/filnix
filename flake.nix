{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    filc-src = {
      url = "github:pizlonator/fil-c";
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

    # Filtered source paths to reduce disk usage
    filc-llvm-src = "${filc-src}/llvm";
    filc-libpas-src = "${filc-src}/libpas";
    filc-runtime-src = "${filc-src}/filc";

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
    filc0 = mkFilcLLVMBuild {
      pname = "filc0";
      cmakeSource = "llvm";
      ninjaTargets = ["clang"];
      installTargets = ["install-clang" "install-clang-resource-headers"];
      preConfigure = ''
        mkdir -p pizfix/lib
        for x in ${gcc-lib}/*.o; do
          cp $x pizfix/lib/
        done
      '';
      cmakeOptions = {
        LLVM_ENABLE_PROJECTS = "clang";
      };
      meta.description = "Fil-C Clang compiler (LLVM stage only)";
    };

    # From the bare compiler, we can create the first Pizfix slice,
    # which adds the basic yolo runtime, headers, etc.
    #
    # This depends on yolo-glibc, so it will automatically build that.
    filc1 = mkFilcClang (mkPizfix {});

    # Using that compiler, we can create the second Pizfix slice,
    # which adds the Fil-C runtime, compiled using filc1.
    filc2 = mkFilcClang (mkPizfix { filcRuntimeLibs = libpizlo; });

    # This next compiler fills out the Pizfix structure now also
    # with the Fil-C safe glibc, which I for some reason started
    # calling "libmojo".
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
    filc-libcxx = mkFilcLLVMBuild {
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
        LIBCXX_ENABLE_WIDE_CHARACTERS = false;
        LIBCXX_INCLUDE_TESTS = false;
        LIBCXX_INCLUDE_BENCHMARKS = false;
        CMAKE_C_COMPILER = "${filc3}/bin/clang";
        CMAKE_CXX_COMPILER = "${filc3}/bin/clang";
        CMAKE_C_FLAGS = "-isystem ${libmojo}/include";
        CMAKE_CXX_FLAGS = "-isystem ${libmojo}/include";
      };
      meta.description = "Fil-C LLVM C++ runtimes";      
    };

    # Build pizfix directory structure (Fil-C's custom layout)
    # It's what the Fil-C driver discovers at binary/../../../pizfix.
    mkPizfix = { filcRuntimeLibs ? null }: base.runCommand "pizfix" {
      nativeBuildInputs = [base.rsync];
    } ''
      mkdir -p $out/{lib,yolo-include,os-include,stdfil-include}
      
      # Libraries: yolo + gcc crt files + optional filc runtime
      rsync -a ${libyolo}/lib/ $out/lib/
      chmod -R u+w $out/lib
      cp ${gcc-lib}/crt*.o $out/lib/
      cp ${gcc-lib}/libgcc* $out/lib/ || true
      mkdir -p $out/lib/gcc/${targetPlatform}/${gcc.version}
      cp -r ${gcc-lib}/* $out/lib/gcc/${targetPlatform}/${gcc.version}/
      
      ${lib.optionalString (filcRuntimeLibs != null) ''
        cp ${filcRuntimeLibs}/lib/filc_crt.o $out/lib/ || true
        cp ${filcRuntimeLibs}/lib/filc_mincrt.o $out/lib/ || true
        cp ${filcRuntimeLibs}/lib/libpizlo.so $out/lib/ || true
        cp ${filcRuntimeLibs}/lib/libpizlo.a $out/lib/ || true
      ''}
      
      # Headers
      rsync -a ${libyolo-glibc}/include/ $out/yolo-include/
      rsync -a ${base.linuxHeaders}/include/ $out/os-include/
      cp ${filc-src}/filc/include/*.h $out/stdfil-include/
    '';

    # Assemble Fil-C compiler: clang binary + pizfix directory.
    # This also guarantees a consistent GCC toolchain baked into
    # the Clang driver, along with the core compiler header path.
    mkFilcClang = pizfix: base.runCommand "pizfix-filc" {
      nativeBuildInputs = [base.makeWrapper];
    } ''
      mkdir -p $out/clang/bin
      cp -r ${pizfix} $out/pizfix
      chmod -R u+w $out/pizfix
      
      # Copy clang binary
      cp ${filc0}/bin/clang-${llvmMajor} $out/clang/bin/clang-${llvmMajor}
      chmod +x $out/clang/bin/clang-${llvmMajor}
      
      # Hardcode paths for deterministic builds
      wrapProgram $out/clang/bin/clang-${llvmMajor} \
        --add-flags "--gcc-toolchain=${gcc.cc}" \
        --add-flags "-resource-dir ${filc0}/lib/clang/${llvmMajor}"
      
      # Convenience symlinks
      mkdir -p $out/bin
      ln -s ../clang/bin/clang-${llvmMajor} $out/bin/clang
      ln -s ../clang/bin/clang-${llvmMajor} $out/bin/clang++
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

    # We then take the Fil-C glibc yolo fork and rename its
    # components so they don't conflict with the normal glibc.
    libyolo = let
      # Here's a little declaration of the new renamed artifacts,
      # along with link-time dependencies and linker scripts.
      libs = {
        # The dynamic linker module itself.
        "ld-yolo-x86_64.so" = {
          source = "ld-linux-x86-64.so.2";
          # No RPATH on the linker!
          stripRpath = true;
        };

        # The base glibc implementation.
        "libyolocimpl.so" = {
          source = "libc.so.6";
          # Rename the linker dependency.
          deps = { "ld-linux-x86-64.so.2" = "ld-yolo-x86_64.so"; };
          # Set a relative RPATH; the file itself has a constant Nix store path.
          setRpath = "$ORIGIN";
        };

        # Math library.
        "libyolomimpl.so" = {
          source = "libm.so.6";
          deps = {
            "ld-linux-x86-64.so.2" = "ld-yolo-x86_64.so";
            "libc.so.6" = "libyolocimpl.so";
          };
          setRpath = "$ORIGIN";  # Find ld-yolo in same directory
        };

        # I wonder what this indirection is for!
        "libyolom.so" = {
          linkerScript = {
            libs = ["libyolomimpl.so"];
          };
        };

        # A shared bundle defined by a linker script.        
        "libyoloc.so" = {
          linkerScript = {
            libs = ["libyolocimpl.so" "libyoloc_nonshared.a"];
            asNeeded = ["ld-yolo-x86_64.so"];
          };
        };

        # Static variants.
        "libyoloc.a" = { source = "libc.a"; };
        "libyoloc_nonshared.a" = { source = "libc_nonshared.a"; };
        "libyolom.a" = {  source = "libm.a"; };
      };

      # Now we just have to transform the beautiful declarative structure
      # into a bash script...

      # Separate libs with sources vs linker scripts
      sourceLibs = lib.filterAttrs (name: def: def ? source) libs;
      scriptLibs = lib.filterAttrs (name: def: def ? linkerScript) libs;

      # Generate copy commands for source-based libs
      copyCmds = lib.mapAttrsToList 
        (name: def: "cp ${libyolo-glibc}/lib/${def.source} $out/lib/${name}") 
        sourceLibs;
      
      # Generate patchelf commands for updating dependencies
      depPatchCmds = lib.mapAttrsToList (name: def:
        if def ? deps then
          lib.mapAttrsToList 
            (old: new: "patchelf --replace-needed ${old} ${new} $out/lib/${name}") 
            def.deps
        else []
      ) libs;

      # Generate soname update commands
      sonameCmds = lib.mapAttrsToList (name: def:
        if def ? deps then "patchelf --set-soname ${name} $out/lib/${name}" else ""
      ) libs;

      # Generate rpath commands (strip or set)
      rpathCmds = lib.mapAttrsToList (name: def:
        if def ? stripRpath && def.stripRpath then
          "patchelf --remove-rpath $out/lib/${name}"
        else if def ? setRpath then
          "patchelf --set-rpath '${def.setRpath}' $out/lib/${name}"
        else ""
      ) libs;

      # Combine all commands
      allCmds = 
        copyCmds ++ 
        ["chmod -R u+w $out/lib"] ++
        (lib.flatten depPatchCmds) ++ 
        (lib.filter (s: s != "") sonameCmds) ++
        (lib.filter (s: s != "") rpathCmds);

      # Render a linker script from a spec
      mkLinkerScript = name: spec:
        let
          libsList = join " " spec.libs;
          asNeeded = if spec ? asNeeded then " AS_NEEDED(${join " " spec.asNeeded})" else "";
        in base.writeText name ''
          OUTPUT_FORMAT(elf64-x86-64)
          GROUP(${libsList}${asNeeded})
        '';

      # Generate linker scripts from libs definitions
      linkerScripts = lib.mapAttrs (name: def: mkLinkerScript name def.linkerScript) scriptLibs;
    in
      base.runCommand "libyolo" {
        nativeBuildInputs = [base.patchelf];
      } ''
        mkdir -p $out/lib
        cp ${libyolo-glibc}/lib/*.o $out/lib/

        # Copy, patch, and configure libraries
        ${lib.concatStringsSep "\n        " allCmds}

        # Install linker scripts for libc and libm
        ${lib.concatStringsSep "\n        " 
          (lib.mapAttrsToList (name: file: "cp ${file} $out/lib/${name}") linkerScripts)}
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
    libpizlo = base.stdenv.mkDerivation {
      pname = "libpizlo";
      version = "git";
      src = filc-src;
      
      sourceRoot = "source/libpas";
      
      nativeBuildInputs = with base; [
        gnumake ruby base-clang binutils rsync ccache
      ];

      postUnpack = ''
        # Make source writable (it's read-only from Nix store)
        chmod -R u+w source
        
        # libpas Makefile expects ../pizfix with yolo-include/os-include subdirs
        mkdir -p source/pizfix
        rsync -a ${libyolo}/lib/ source/pizfix/lib/
        rsync -a ${libyolo-glibc}/include/ source/pizfix/yolo-include/
        rsync -a ${base.linuxHeaders}/include/ source/pizfix/os-include/
        mkdir -p source/pizfix/stdfil-include
        
        # Makefile builds multiple library variants
        mkdir -p source/pizfix/lib_test
        mkdir -p source/pizfix/lib_gcverify
        mkdir -p source/pizfix/lib_test_gcverify
        
        chmod -R u+w source/pizfix
        
        # Also expects ../filc/src and ../filc/include
        mkdir -p source/filc/include
        mkdir -p source/filc/src
        mkdir -p source/filc/main
        cp ${filc-src}/filc/include/*.h source/filc/include/
        cp ${filc-src}/filc/src/*.c source/filc/src/
        cp ${filc-src}/filc/main/*.c source/filc/main/
        
        # Pattern rule depends on ../build/bin/clang existing
        mkdir -p source/build/bin
        ln -s ${filc1}/bin/clang source/build/bin/clang
      '';

      preConfigure = ''
        export HOME=$TMPDIR
        export HOSTNAME=nix-build
        
        # Set up ccache
        ${setupCcache}
        export CC="ccache clang"
        export CXX="ccache clang++"
        
        patchShebangs *.rb *.sh
      '';

      buildPhase = ''
        mkdir -p build
        make -f Makefile-setup
        make -j$NIX_BUILD_CORES FILCFLAGS="-O3 -g -W -Werror -MD -I../filc/include"
      '';

      installPhase = ''
        mkdir -p $out/lib $out/include
        cp ../pizfix/lib/libpizlo.so $out/lib/
        cp ../pizfix/lib/libpizlo.a $out/lib/
        cp ../pizfix/lib/filc_crt.o $out/lib/
        cp ../pizfix/lib/filc_mincrt.o $out/lib/ || true
        cp ../pizfix/stdfil-include/*.h $out/include/
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
      ln -s ${filc2}/bin/clang $out/bin/clang
      ln -s ${filc2}/bin/clang $out/bin/gcc
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

    # Now we can define a Nix conventional C++ toolchain!
    filcc = base.wrapCCWith {
      cc       = filc-cc;
      libc     = filc-sysroot;
      bintools = filc-bintools;
      isClang  = true;

      extraBuildCommands = ''
        echo "-Wno-unused-command-line-argument" >> $out/nix-support/cc-cflags
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

    debug = pkg: pkg.overrideAttrs (old: {
      nativeBuildInputs = old.nativeBuildInputs or [] ++ [base.pkgs.breakpointHook];
    });

    # experimental full Fil-C nixpkgs
    filpkgs = import nixpkgs {
      inherit system;
      config.replaceStdenv = { pkgs, ... }:
        pkgs.overrideCC pkgs.stdenv filcc;
    };

  in {
    # Finally, we define the package collection!
    packages.${system} = rec {
      inherit filpkgs;

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

      # Some easy ones to get started!
      gawk = parallelize (withFilC base.gawk);
      gnused = parallelize (withFilC base.gnused);
      gnutar = parallelize (withFilC base.gnutar);
      bzip2 = parallelize (withFilC base.bzip2);

      readline = (withFilC base.readline).override {
        inherit ncurses;
      };

      # Nethack works!
      nethack = (withFilC base.nethack).override {
        inherit ncurses;
      };

      lua5 = (withFilC base.lua).override {
        inherit readline;
      };

      coreutils = withFilC base.coreutils;

      bash = ((withFilC base.bash).overrideAttrs (old: {
        patches = (old.patches or []) ++ [
          ./patches/bash-5.2.32-filc.patch
        ];
      })).override {
        inherit readline;
      };

      quickjs = withFilC base.quickjs; # slow build
      sqlite = withFilC base.sqlite;   # slow build

      curl = 
        filenv.mkDerivation (final: {
          src = "${filc-src}/projects/curl-${final.version}";
          pname = "curl";
          version = "8.9.1";
          enableParallelBuilding = true;
          configureFlags = [
            "--with-openssl"
            "--with-zlib"
            "--with-ca-bundle=${base.cacert}/etc/ssl/certs/ca-bundle.crt"
          ];
          doCheck = false;
          nativeBuildInputs = with base; [
            perl pkg-config
          ];
          buildInputs = [openssl libtool zlib];
          patchPhase = ''
            patchShebangs scripts
          '';
        });


      openssl-nix = withFilC base.openssl;

      openssl = 
        filenv.mkDerivation (final: {
          src = "${filc-src}/projects/openssl-${final.version}";
          pname = "openssl";
          version = "3.3.1";
          enableParallelBuilding = true;
          nativeBuildInputs = with base; [perl];
          buildInputs = [zlib];
          configurePhase = ''
            ./Configure zlib --prefix=$out --libdir=$out/lib
          '';
          patchPhase = ''
            patchShebangs .
          '';
          buildPhase = "make -j$NIX_BUILD_CORES";
          installPhase = ''
            make -j$NIX_BUILD_CORES install_sw
            make -j$NIX_BUILD_CORES install_ssldirs
          '';
        });


      pcre2 = withFilC base.pcre2;

      nginx = ((withFilC base.nginx).override {
        inherit openssl pcre2 zlib-ng;
      });

      libxcrypt = filc-xcrypt;

      ncurses = withFilC base.ncurses;
      libutempter = withFilC base.libutempter;
      utf8proc = withFilC base.utf8proc;
      libevent = (withFilC base.libevent).override {
        sslSupport = false;
      };

      tmux = ((withFilC base.tmux).override {
        inherit ncurses libevent libutempter utf8proc;
        withSystemd = false;
      });

      zlib = withFilC base.zlib;
      zlib-ng = withFilC base.zlib-ng; # needs c++

      libtool = withFilC base.libtool;

      graphviz = ((withFilC base.graphviz).overrideAttrs (_: {
        buildInputs = [bash];
        nativeBuildInputs = with base; [
          autoreconfHook  autoconf python3 bison flex pkg-config libtool
        ];
        configureFlags = ["--without-x"];
      }));

      libpng = 
        filenv.mkDerivation (final: {
          src = "${filc-src}/projects/libpng-${final.version}";
          pname = "libpng";
          version = "1.6.43";
          enableParallelBuilding = true;
          configureFlags = [
          ];
          nativeBuildInputs = with base; [
            pkg-config
          ];
          buildInputs = [
            zlib
          ];
        });

      # doesn't build
      libjpeg = (withFilC base.libjpeg).overrideAttrs (_: {
        doCheck = false;
      });
    };

    devShells.${system}.default = filenv.mkDerivation {
      name = "filc";
      buildInputs = [ ];
      shellHook = ''
        echo "Fil-C development environment"
        echo "Compiler: $(type -p clang)"
        clang --version | head -1
        echo
      '';
    };
  };
}
