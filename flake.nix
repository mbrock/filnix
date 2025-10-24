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

    # stripped down version of Fil-C's build script
    # to only build the compiler
    filc-clang-only = base.stdenv.mkDerivation {
      pname = "filc-clang";
      version = "git";
      src = filc-src;

      nativeBuildInputs = with base; [
        cmake
        ninja
        python3
        git
        patchelf
      ];

      hardeningDisable = [ "fortify" "stackprotector" "pie" ];

      ALTLLVMLIBCOPT = " ";

      configurePhase = ''
        runHook preConfigure

        export HOME=$TMPDIR
        export HOSTNAME=nix-build

        # Only unset the problematic CFLAGS that add gcc headers
        unset NIX_CFLAGS_COMPILE NIX_CXXSTDLIB_COMPILE

        patchShebangs configure_llvm.sh build_clang.sh libpas/common.sh

        runHook postConfigure
      '';

      buildPhase = ''
        runHook preBuild

        echo "Configuring LLVM..."
        ./configure_llvm.sh

        echo "Building Clang (this takes ~20 minutes)..."
        ./build_clang.sh

        runHook postBuild
      '';

      installPhase = ''
        runHook preInstall

        mkdir -p $out
        cp -r build $out/build

        # Patch ELF binaries
        for exe in $out/build/bin/*; do
          if [ -x "$exe" ] && file "$exe" | grep -q ELF; then
            patchelf --set-rpath "$out/build/lib" "$exe" || true
          fi
        done

        runHook postInstall
      '';

      enableParallelBuilding = true;

      meta.description = "Fil-C Clang compiler (LLVM stage only)";
    };

    # hmm, we can build this as a basically standard derivation
    # with the gcc from stdenv; yolo!
    yolo-glibc = base.stdenv.mkDerivation {
      pname = "yolo-glibc";
      version = "git";
      src = "${filc-src}/projects/yolo-glibc-2.40";

      nativeBuildInputs = with base; [
        python3
        git
        file
        patchelf
        gnumake
        pkg-config
        autoconf
        bison
      ];

      preConfigurePhases = ["autoconf"];
      autoconf = ''
        autoconf
        configureScript=`pwd`/configure
        mkdir ../build
        cd ../build
      '';

      configureFlags = ["--disable-mathvec"];
      hardeningDisable = [ "fortify" "stackprotector" "pie" ];
      enableParallelBuilding = true;
      doCheck = false;

      meta.description = "Fil-C Yolo glibc";
    };

    # this packages up the previous things into something
    # resembling a preliminary pizfix slice
    # without the user glibc
    filc-yolo-libc = base.runCommand "filc-yolo-libc" {
      nativeBuildInputs = [base.patchelf base.file];
    } ''
      mkdir -p $out/lib
      cp -R ${yolo-glibc}/include $out/yolo-include
      cp -R ${base.linuxHeaders}/include $out/os-include
      cp -R ${clang-include} $out/include

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
    '';

    clang-rsrc = base.lib.getLib base.llvmPackages_20.clang.cc;
    clang-include = "${clang-rsrc}/lib/clang/20/include";
    glibc-include = "${base.lib.getInclude base.glibc}/include";
    gcc-lib = "${base.gcc.cc}/lib/gcc/x86_64-unknown-linux-gnu/14.3.0/";

    base-clang = base.writeShellScriptBin "clang" ''
      exec ${base.llvmPackages_20.clang.cc}/bin/clang -isystem ${clang-include} "$@"
    '';

    # hmm, this builds the libpas/runtime (libpizlo etc)
    # into a fuller pizfix slice to be used in the next step
    # which actually builds glibc with Fil-C clang
    filc-runtime = base.runCommand "filc-libpas" {
      nativeBuildInputs = with base; [
        gnumake
        base-clang
        ruby
        glibc.dev
        binutils
      ];
    } ''
      export HOME=$TMPDIR
      export HOSTNAME=nix-build

      mkdir -p $out/build
      cd $out

      cp -r ${filc-src}/libpas .
      cp -r ${filc-src}/filc .
      cp -r ${filc-yolo-libc} pizfix
      cp -r ${filc-clang-only}/build/bin $out/build/

      chmod -R u+w .

      cd libpas
      patchShebangs *.rb
      ./clean.sh
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
      mkdir -p $out
      cp -r ${filc-src}/projects/user-glibc-2.40 $out/src
      cd $out/src
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
      EXTRASTUFF="-isystem ${clang-include} -B ${gcc-lib} -L ${gcc-lib}"

      export CC="${filc-runtime}/build/bin/clang $FILCFLAGS $EXTRASTUFF"
      export CXX="${filc-runtime}/build/bin/clang++ $FILCXXFLAGS $EXTRASTUFF"

      ../src/configure --prefix=$out --disable-mathvec

      make install -j$NIX_BUILD_CORES

      # clean up after installing the artifacts
      rm -rf src build

      for exe in $out/bin/* $out/lib/*; do
        if [ -x "$exe" ] && file "$exe" | grep -q ELF; then
          echo shrinking rpath of $exe
          patchelf --shrink-rpath "$exe" || true
        fi
      done 
    '';

    # this fails, for the same reason the user glibc build is 
    # producing binaries that can't execute;
    # the dynamic linker triggers an assertion RUNPATH != null
    # in some kind of "bootstrap" related check?
    filc-xcrypt = base.runCommand "filc-xcrypt" {
      nativeBuildInputs = with base; [
        gnumake
        binutils
      ];
    } ''
      mkdir -p $out
      cd $TMPDIR
      cp -r ${filc-src}/projects/libxcrypt-4.4.36 src
      cd src
      chmod -R u+w .

      EXTRASTUFF="-isystem ${clang-include} -B ${gcc-lib} -L ${gcc-lib} -L ${filc-glibc}/lib -I${filc-glibc}/include"
      export CC="${filc-runtime}/build/bin/clang $EXTRASTUFF"

      ./configure --prefix=$out
      make install -j$NIX_BUILD_CORES

      for exe in $out/bin/* $out/lib/*; do
        if [ -x "$exe" ] && file "$exe" | grep -q ELF; then
          echo shrinking rpath of $exe
          patchelf --shrink-rpath "$exe" || true
        fi
      done 
    '';

    ##### everything below here is from the old flake variant
    ##### that used the binary pizfix distribution
    ##### and is now deprecated and doesn't work sadly!

    filc-clang = base.writeShellScriptBin "clang" ''
      exec ${filc-clang-only}/build/bin/clang "$@"
    '';

    filc-clangpp = base.writeShellScriptBin "clang++" ''
      exec ${filc-clang-only}/build/bin/clang++ "$@"
    '';

    filc-unwrapped = filc-clang-only;

    filc-cc = base.runCommand "filc-cc" {
      nativeBuildInputs = [base.patchelf base.file];
    } ''
      mkdir -p $out
      cp -r ${filc-unwrapped}/build $out/build
      cp -r ${filc-unwrapped}/pizfix $out/pizfix
      mkdir $out/bin
      echo exec $out/build/bin/clang '"$@"' > $out/bin/clang
      echo exec $out/build/bin/clang++ '"$@"' > $out/bin/clang++
      chmod +x $out/bin/*

      for exe in $out/pizfix/bin/*; do
        if [ -x "$exe" ] && file "$exe" | grep -q ELF; then
          chmod u+w $exe
          patchelf --set-interpreter ${filc-libc}/lib/ld-yolo-x86_64.so $exe
          patchelf --set-rpath $out/pizfix/lib $exe
        fi
      done

     for exe in $out/build/bin/*; do
       if [ -x "$exe" ] && file "$exe" | grep -q ELF; then
         chmod u+w $exe
         patchelf --set-interpreter ${base.glibc.out}/lib/ld-linux-*.so.2 $exe
         patchelf --set-rpath $out/pizfix/lib $exe
       fi
     done
    '';

    # not sure how this interacts with fil-c slice detection etc
    filc-libc = base.runCommand "filc-libc" {} ''
      set -euo pipefail
      mkdir -p $out/{include,lib} $out/nix-support
      cp -r ${filc-unwrapped}/pizfix/include/. $out/include/ 2>/dev/null || true
      cp -r ${filc-unwrapped}/pizfix/lib/.     $out/lib/     2>/dev/null || true
      cp -r ${filc-unwrapped}/pizfix/stdfil-include/. $out/include/ 2>/dev/null || true        

      echo "$out/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
      ln -s "$out/lib/ld-yolo-x86_64.so" "$out/lib/ld-linux-x86-64.so.2"

      for crt in crt1.o rcrt1.o Scrt1.o crti.o crtn.o; do
        if [ -f "$out/lib/$crt" ]; then
          echo "$out/lib/$crt" > "$out/nix-support/$crt"
        fi
      done
    '';

    filc-bintools = base.wrapBintoolsWith {
      bintools = base.binutils;
      libc     = filc-libc;
    };

    filc-wrapped = base.wrapCCWith {
      cc       = filc-cc.overrideAttrs (old: {
        passthru = (old.passthru or {}) // {
          libllvm = base.llvmPackages_20.libllvm;
        };
      });
      libc     = filc-libc;
      bintools = filc-bintools;
      isClang  = true;

      extraBuildCommands = ''
        echo "-gz=none" >> $out/nix-support/cc-cflags
        echo "-Wl,--compress-debug-sections=none" >> $out/nix-support/cc-cflags
        echo "-L${filc-libc}/lib" >> $out/nix-support/cc-cflags
        echo "-rpath ${filc-libc}/lib" >> $out/nix-support/cc-ldflags
        ln -s clang $out/bin/gcc
        ln -s clang++ $out/bin/g++
      '';    
    };

    filc-compat = filc-wrapped.overrideAttrs (old: {
      passthru = (old.passthru or {}) // {
        libllvm = base.llvmPackages_20.libllvm; # hee hee
      };
    });

    # Fil-C stdenv
    filenv = base.overrideCC base.stdenv filc-compat;

    # turn a package into a Fil-C package
    withFilC = pkg: pkg.override { stdenv = filenv; };

    # experimental full Fil-C nixpkgs
    filpkgs = import nixpkgs {
      inherit system;
      config.replaceStdenv = { pkgs, ... }:
        pkgs.overrideCC pkgs.stdenv filc-compat;
    };
  in {
    packages.${system} = rec {
      inherit filpkgs;

      inherit filc-unwrapped;
      inherit filc-clang-only;
      inherit yolo-glibc;
      inherit filc-runtime;
      inherit filc-glibc;
      inherit filc-xcrypt;

      # at least these definitely work
      gawk = withFilC base.gawk;
      gnused = withFilC base.gnused;
      gnutar = withFilC base.gnutar;
      bzip2 = withFilC base.bzip2;

      # builds! but crashes with a termios related syscall?
      lua = (withFilC base.lua).override {
        inherit readline;
      };

      # bash with fil-c alignment patch,
      # same crash as lua
      bash = (withFilC base.bash).overrideAttrs (old: {
        patches = (old.patches or []) ++ [
          ./patches/bash-5.2.32-filc.patch
        ];
      });

      quickjs = withFilC base.quickjs; # slow build
      sqlite = withFilC base.sqlite;   # slow build

      # fails, its own libcurl doesn't have fil-c mangling? i dunno
      curl = (withFilC base.curlMinimal).override {
        gssSupport = false;
        opensslSupport = false;
        gnutlsSupport = false;
        pslSupport = false;
        http2Support = false;
        zlibSupport = false;
      };

      openssl = withFilC base.openssl;
      pcre2 = withFilC base.pcre2;

      nginx = (withFilC base.nginx).override {
        inherit openssl pcre2;
      };

      readline = (withFilC base.readline).override {
        inherit ncurses;
      };

      nethack = withFilC base.nethack;
      ncurses = withFilC base.ncurses;

      # tmux didn't manage to use these
      libutempter = withFilC base.libutempter;
      utf8proc = withFilC base.utf8proc;

      # forkpty errors that actually mean configure failed to link stuff
      tmux = ((withFilC base.tmux).override {
        inherit ncurses;
        withSystemd = false;
        withUtempter = false;
        withUtf8proc = false;
      }).overrideAttrs (_: {

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
