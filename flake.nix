{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    filc-src = {
      url = "git+file:///home/mbrock/fil-c";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, filc-src, ... }:
  let
    system = "x86_64-linux";
    base = import nixpkgs { inherit system; };
    lib = base.lib;
    join = lib.concatStringsSep;

    filc-libcxx = base.ccacheStdenv.mkDerivation {
      pname = "filc-libcxx";
      version = "git";
      src = filc-src;

      nativeBuildInputs = with base; [
        cmake ninja python3 git patchelf ccache mold
      ];

      preBuild = ''
        export CCACHE_COMPRESS=1
        export CCACHE_SLOPPINESS=random_seed
        export CCACHE_DIR="/nix/var/cache/ccache"
        export CCACHE_UMASK=007      
      '';

      configurePhase = ''
        runHook preConfigure
        export HOME=$TMPDIR
        export HOSTNAME=nix-build
        runHook postConfigure
      '';

      buildPhase = let 
        commonOptions = [
          "-DCMAKE_BUILD_TYPE=RelWithDebInfo" 
          "-DLLVM_ENABLE_ASSERTIONS=ON"
          "-DLLVM_ENABLE_WARNINGS=OFF"
          "-DLLVM_ENABLE_ZSTD=OFF"
          "-DLLVM_TARGETS_TO_BUILD=X86"
          "-DLLVM_ENABLE_LIBXML2=OFF"
          "-DLLVM_ENABLE_LIBEDIT=OFF"
          "-DLLVM_ENABLE_LIBPFM=OFF"
          "-DLLVM_ENABLE_ZLIB=OFF"
          "-DLLVM_ENABLE_ZSTD=OFF"
          "-DLLVM_ENABLE_CURL=OFF"
          "-DLLVM_ENABLE_HTTPLIB=OFF"
          "-DLLVM_STATIC_LINK_CXX_STDLIB=ON"
          "-DCMAKE_EXE_LINKER_FLAGS=-static-libgcc"
          "-DCMAKE_INSTALL_PREFIX=$out"
          "-DLLVM_USE_LINKER=mold"
        ];
        libcxxOptions = commonOptions ++ [
          "-DLLVM_ENABLE_RUNTIMES=libcxx;libcxxabi"
          "-DLIBCXXABI_HAS_PTHREAD_API=ON" 
          "-DLIBCXX_ENABLE_EXCEPTIONS=ON"
          "-DLIBCXXABI_ENABLE_EXCEPTIONS=ON" 
          "-DLIBCXX_HAS_PTHREAD_API=ON"
          "-DLIBCXXABI_USE_LLVM_UNWINDER=OFF"
          "-DLIBCXX_FORCE_LIBCXXABI=ON"
        ];
      in '' 
        runHook preBuild
        mkdir build
        cmake -B build -S llvm -G Ninja $cmakeFlags ${join " " clangOptions}
        NINJA_STATUS="[%f/%t %es] " ninja -v -C build runtimes
        runHook postBuild
      '';

      installPhase = ''
        runHook preInstall
        ninja -C build install
        runHook postInstall
      '';

      enableParallelBuilding = true;

      meta.description = "Fil-C LLVM C++ runtimes";      
    };

    # stripped down version of Fil-C's build script
    # to only build the compiler
    filc-clang-only = base.ccacheStdenv.mkDerivation {
      pname = "filc-clang";
      version = "git";
      src = filc-src;

      nativeBuildInputs = with base; [
        cmake
        ninja
        python3
        git
        patchelf
        ccache
        makeWrapper
        mold
      ];

      hardeningDisable = [ "fortify" "stackprotector" "pie" ];

      ALTLLVMLIBCOPT = " ";

      preBuild = ''
        export CCACHE_COMPRESS=1
        export CCACHE_SLOPPINESS=random_seed
        export CCACHE_DIR="/nix/var/cache/ccache"
        export CCACHE_UMASK=007
      '';

      configurePhase = ''
        runHook preConfigure

        export HOME=$TMPDIR
        export HOSTNAME=nix-build

        # pretend to be a pizfix to avoid having to change toolchain search logic
        mkdir -p pizfix/lib
        for x in ${gcc-lib}/*.o; do
          echo copying $x
          cp $x pizfix/lib/
        done

        patchShebangs configure_llvm.sh build_clang.sh libpas/common.sh

        runHook postConfigure
      '';

      buildPhase = let 
        commonOptions = [
          "-DCMAKE_BUILD_TYPE=RelWithDebInfo" 
          "-DLLVM_ENABLE_ASSERTIONS=ON"
          "-DLLVM_ENABLE_WARNINGS=OFF"
          "-DLLVM_ENABLE_ZSTD=OFF"
          "-DLLVM_TARGETS_TO_BUILD=X86"
          "-DLLVM_ENABLE_LIBXML2=OFF"
          "-DLLVM_ENABLE_LIBEDIT=OFF"
          "-DLLVM_ENABLE_LIBPFM=OFF"
          "-DLLVM_ENABLE_ZLIB=OFF"
          "-DLLVM_ENABLE_ZSTD=OFF"
          "-DLLVM_ENABLE_CURL=OFF"
          "-DLLVM_ENABLE_HTTPLIB=OFF"
          "-DLLVM_STATIC_LINK_CXX_STDLIB=ON"
          "-DCMAKE_EXE_LINKER_FLAGS=-static-libgcc"
          "-DCMAKE_INSTALL_PREFIX=$out"
          "-DLLVM_USE_LINKER=mold"
        ];
        clangOptions = commonOptions ++ [
          "-DLLVM_ENABLE_PROJECTS=clang"
        ];
        libcxxOptions = commonOptions ++ [
          "-DLLVM_ENABLE_RUNTIMES=libcxx;libcxxabi"
          "-DLIBCXXABI_HAS_PTHREAD_API=ON" 
          "-DLIBCXX_ENABLE_EXCEPTIONS=ON"
          "-DLIBCXXABI_ENABLE_EXCEPTIONS=ON" 
          "-DLIBCXX_HAS_PTHREAD_API=ON"
          "-DLIBCXXABI_USE_LLVM_UNWINDER=OFF"
          "-DLIBCXX_FORCE_LIBCXXABI=ON"
        ];
      in '' 
        runHook preBuild
        mkdir build
        cmake -B build -S llvm -G Ninja $cmakeFlags ${join " " clangOptions}
        NINJA_STATUS="[%f/%t %es] " ninja -v -C build clang
        runHook postBuild
      '';

      installPhase = ''
        runHook preInstall
        ninja -C build install
        runHook postInstall
      '';

      enableParallelBuilding = true;

      meta.description = "Fil-C Clang compiler (LLVM stage only)";
    };
            
    yolo-glibc = base.runCommand "yolo-glibc" {
      nativeBuildInputs = with base; [
        python3
        git
        file
        patchelf
        gnumake
        pkg-config
        autoconf
        bison
        gcc-unwrapped
        binutils-unwrapped
      ];
    } ''
      export HOME=$TMPDIR
      export HOSTNAME=nix-build
      cd $TMPDIR
      cp -R ${filc-src}/projects/yolo-glibc-2.40 src
      cd src
      chmod -R u+w .
      autoconf
      mkdir ../build
      cd ../build
      export NIX_CFLAGS_COMPILE=""
      export NIX_LDFLAGS=""
      ../src/configure --disable-mathvec --disable-nscd --prefix=$out --disable-werror \
        libc_cv_slibdir=$out/lib \
        --with-headers=${base.linuxHeaders}/include
      make -j$NIX_BUILD_CORES
      make install
    '';

    # this packages up the previous things into something
    # resembling a preliminary pizfix slice
    # without the user glibc
    filc-yolo-libc = base.runCommand "filc-yolo-libc" {
      nativeBuildInputs = [base.patchelf base.file];
    } ''
      mkdir -p $out/lib
      cp -R ${yolo-glibc}/include $out/yolo-include
      cp -R ${base.linuxHeaders}/include $out/os-include
      cp -R ${filc-src}/clang/lib/Headers $out/include

      OLDLDNAME=ld-linux-x86-64.so.2
      OLDLIBCIMPLNAME=libc.so.6
      OLDLIBCNONSHAREDNAME=libc_nonshared.a
      OLDLIBMIMPLNAME=libm.so.6
      OLDSTATICLIBCNAME=libc.a
      OLDSTATICLIBMNAME=libm.a

      LDNAME=ld-yolo-x86_64.so
      LIBNAMEBASE=libyolo
      LIBCNAMEBASE=libyoloc
      LIBCNAME=libyoloc.so
      LIBCIMPLNAME=libyolocimpl.so
      LIBCNONSHAREDNAME=libyoloc_nonshared.a
      LIBMIMPLNAME=libyolomimpl.so
      LIBMNAME=libyolom.so
      STATICLIBCNAME=libyoloc.a
      STATICLIBMNAME=libyolom.a

      cd ${yolo-glibc}/lib
      cp $OLDLDNAME $out/lib/$LDNAME
      cp $OLDLIBCIMPLNAME $out/lib/$LIBCIMPLNAME
      cp $OLDLIBCNONSHAREDNAME $out/lib/$LIBCNONSHAREDNAME
      cp $OLDLIBMIMPLNAME $out/lib/$LIBMIMPLNAME
      cp *.o $out/lib/
      cp $OLDSTATICLIBCNAME $out/lib/$STATICLIBCNAME
      cp $OLDSTATICLIBMNAME $out/lib/$STATICLIBMNAME

      cd $out/lib
      chmod -R u+w .
      patchelf --replace-needed $OLDLDNAME $LDNAME $LIBCIMPLNAME
      patchelf --set-soname $LIBCIMPLNAME $LIBCIMPLNAME
      patchelf --set-soname $LDNAME $LDNAME
      patchelf --replace-needed $OLDLDNAME $LDNAME $LIBMIMPLNAME
      patchelf --replace-needed $OLDLIBCIMPLNAME $LIBCIMPLNAME $LIBMIMPLNAME
      patchelf --set-soname $LIBMIMPLNAME $LIBMIMPLNAME
      echo "OUTPUT_FORMAT(elf64-x86-64)" > $LIBCNAME
      echo "GROUP ( $PWD/$LIBCIMPLNAME $PWD/$LIBCNONSHAREDNAME  AS_NEEDED ( $PWD/$LDNAME ) )" >> $LIBCNAME
      echo "OUTPUT_FORMAT(elf64-x86-64)" > $LIBMNAME
      echo "GROUP ( $PWD/$LIBMIMPLNAME )" >> $LIBMNAME

      patchelf --remove-rpath ld-yolo-x86_64.so
      patchelf --remove-rpath libyolocimpl.so
      patchelf --remove-rpath libyolomimpl.so
    '';

    clang-rsrc = base.lib.getLib base.llvmPackages_20.clang.cc;
    clang-include = "${clang-rsrc}/lib/clang/20/include";
    glibc-include = "${base.lib.getInclude base.glibc}/include";
    gcc-lib = "${base.gcc.cc}/lib/gcc/x86_64-unknown-linux-gnu/14.3.0";
#    gcc-lib = "${base.pkgs.llvmPackages_20.compiler-rt}/lib/linux";

    base-clang = base.writeShellScriptBin "clang" ''
      exec ${base.llvmPackages_20.clang.cc}/bin/clang -isystem ${clang-include} "$@"
    '';

    filc-runtime = base.runCommand "filc-runtime" {
      nativeBuildInputs = with base; [
        gnumake
        base-clang
        ruby
        glibc.dev
        binutils
        patchelf
        makeWrapper
      ];
    } ''
      set -ex
      export HOME=$TMPDIR
      export HOSTNAME=nix-build

      mkdir -p $out/build
      cd $out

      cp -r ${filc-src}/libpas .
      cp -r ${filc-src}/filc .
      cp -r ${filc-yolo-libc} pizfix
      cp -r ${filc-clang-only}/build/bin $out/build/

      chmod -R u+w .

      pushd $out/build/bin
      patchelf --remove-rpath clang-20
      patchelf --set-interpreter $out/pizfix/lib/ld-yolo-x86_64.so clang-20
      patchelf --replace-needed ld-linux-x86-64.so.2 ld-yolo-x86_64.so clang-20
      patchelf --replace-needed libc.so.6 libyolocimpl.so clang-20
      patchelf --replace-needed libm.so.6 libyolomimpl.so clang-20
      wrapProgram `pwd`/clang-20 --set LD_LIBRARY_PATH $out/pizfix/lib
      popd

      cd libpas
      patchShebangs *.rb
      ./build.sh
    '';

    # this uses the Fil-C clang we've built,
    # and the partial pizfix slice with Fil-C runtime,
    # to build the memory-safe glibc...
    #
    # but something is going wrong related to RPATH/RUNPATH
    # that is not solved by my futile patchelf shrinking
    filc-glibc = base.runCommand "filc-glibc" {
      nativeBuildInputs = with base; [
        gnumake
        autoconf
        bison
        python3
        binutils
        glibc.dev
      ];
    } ''
      cd $TMPDIR
      cp -r ${filc-src}/projects/user-glibc-2.40 src
      cd src
      chmod -R u+w .
      autoconf
      cd ..
      mkdir build
      cd build

      # these are from Fil-C's build script
      FILCXXFLAGS="-nostdlibinc -Wno-ignored-attributes -Wno-pointer-sign"
      FILCFLAGS="$FILCXXFLAGS -Wno-unused-command-line-argument -Wno-macro-redefined"

      # these I painstakingly figured out are also necessary in this setup,
      # I'm not sure if it's something missing from my Fil-C Clang configuration
      # or something else, but hey, it seems to work
      EXTRASTUFF="-isystem ${filc-runtime}/pizfix/include --gcc-install-dir=${gcc-lib}"

      export CC="${filc-runtime}/build/bin/clang $FILCFLAGS $EXTRASTUFF"
      export CXX="${filc-runtime}/build/bin/clang++ $FILCXXFLAGS $EXTRASTUFF"

      ../src/configure --prefix=$out --disable-mathvec --disable-nscd --disable-werror \
        libc_cv_slibdir=$out/lib

      make install -j$NIX_BUILD_CORES
    '';

    filc-xcrypt = base.runCommand "filc-xcrypt" {
      nativeBuildInputs = with base; [
        gnumake automake116x autoconf libtool
        binutils
        perl
        python3
      ];
    } ''
      mkdir -p $out
      cd $TMPDIR
      cp -r ${filc-src}/projects/libxcrypt-4.4.36 src
      cd src
      chmod -R u+w .

      EXTRASTUFF="-isystem ${filc-runtime}/pizfix/include --gcc-install-dir=${gcc-lib}"
      EXTRASTUFF+=" -L${filc-glibc}/lib -I${filc-glibc}/include"
      export CC="${filc-runtime}/build/bin/clang $EXTRASTUFF"

      rm aclocal.m4
      libtoolize --copy --force
      autoreconf -vfi -I build-aux/m4
      ./configure --prefix=$out
      make -j$NIX_BUILD_CORES
      make install
    '';

    ##### everything below here is from the old flake variant
    ##### that used the binary pizfix distribution
    ##### and is now deprecated and doesn't work sadly!

    filc-cc = base.runCommand "filc-cc" {} ''
      mkdir -p $out/bin
      ln -s ${filc-runtime}/build/bin/clang-20 $out/bin/clang
      ln -s ${filc-runtime}/build/bin/clang-20 $out/bin/gcc
#      ln -s ${filc-runtime}/build/bin/clang-20 $out/bin/clang++
#      ln -s ${filc-runtime}/build/bin/clang-20 $out/bin/g++
    '';

    # filc-cxx = base.runCommand "filc-cxx" {} ''
    #   mkdir -p $out/bin
    #   ln -s ${filc-runtime}/build/bin/clang-20 $out/bin/clang
    #   ln -s ${filc-runtime}/build/bin/clang-20 $out/bin/gcc
    #   ln -s ${filc-runtime}/build/bin/clang-20 $out/bin/clang++
    #   ln -s ${filc-runtime}/build/bin/clang-20 $out/bin/g++
    # '';

    # hm, stdatomic.h doesn't seem to work, so i delete it
    filc-libc = base.runCommand "filc-libc" {} ''
      set -euo pipefail
      mkdir -p $out/{include,lib,bin} $out/nix-support
      cp -r ${filc-runtime}/pizfix/include/. $out/include/
      cp -r ${filc-runtime}/pizfix/lib/. $out/lib/
      chmod -R u+w $out
      cp -r ${filc-runtime}/pizfix/stdfil-include/. $out/include/
      cp -r ${filc-glibc}/lib/* $out/lib/
      cp -r ${filc-glibc}/bin/* $out/bin/
      rm $out/include/stdatomic.h

      echo "$out/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker

      for crt in crt1.o rcrt1.o Scrt1.o crti.o crtn.o; do
        if [ -f "$out/lib/$crt" ]; then
          echo "$out/lib/$crt" > "$out/nix-support/$crt"
        fi
      done
    '';

    filc-bintools = base.wrapBintoolsWith {
      bintools = base.binutils-unwrapped;
      libc     = filc-libc;

      extraBuildCommands = ''
        echo "-L${filc-glibc}/lib" >> $out/nix-support/libc-ldflags
        echo "${filc-libc}/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
      '';
    };

    filcc = base.wrapCCWith {
      cc       = filc-cc;
      libc     = filc-libc;
      bintools = filc-bintools;
      isClang  = true;

      extraBuildCommands = ''
        echo "-gz=none" >> $out/nix-support/cc-cflags
        echo "-Wl,--compress-debug-sections=none" >> $out/nix-support/cc-cflags
        echo "-isystem ${filc-runtime}/pizfix/include" >> $out/nix-support/cc-cflags
        echo "-isystem ${filc-glibc}/include" >> $out/nix-support/cc-cflags
        echo "--gcc-install-dir=${gcc-lib}" >> $out/nix-support/cc-cflags
        echo "-isystem ${filc-runtime}/pizfix/stdfil-include" >> $out/nix-support/cc-cflags
      '';    
    };

    # Fil-C stdenv
    filenv = base.overrideCC base.stdenv filcc;

    # turn a package into a Fil-C package
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
    packages.${system} = rec {
      inherit filpkgs;

      inherit filc-clang-only;
      inherit yolo-glibc;
      inherit filc-runtime;
      inherit filc-glibc;
      inherit filc-xcrypt;
      inherit filcc;

      gawk = parallelize (withFilC base.gawk);
      gnused = parallelize (withFilC base.gnused);
      gnutar = parallelize (withFilC base.gnutar);
      bzip2 = parallelize (withFilC base.bzip2);

      readline = (withFilC base.readline).override {
        inherit ncurses;
      };

      # nethack works!
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

      # needs c++ compiler
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
