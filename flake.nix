{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    # Git repository for source builds
    filc-src = {
      url = "git+file:///home/mbrock/fil-c";
      flake = false;
    };

    # Optional: keep tarball as fallback
    # filc-tarball = {
    #   url = "tarball+https://github.com/pizlonator/fil-c/releases/download/v0.673/filc-0.673-linux-x86_64.tar.xz";
    #   flake = false;
    # };
  };

  outputs = { self, nixpkgs, filc-src, ... }:
  let
    system = "x86_64-linux";
    base = import nixpkgs { inherit system; };

    # Build fil-c from source with glibc
    filc-unwrapped = base.stdenv.mkDerivation {
      pname = "filc-from-source-glibc";
      version = "git";
      src = filc-src;

      nativeBuildInputs = with base; [
        cmake
        ninja
        python3
        git
        file
        patchelf
        gnumake
        pkg-config
      ];

      buildInputs = with base; [
        glibc
        glibc.static
      ];

      # Disable fortify and hardening that might interfere with fil-c
      hardeningDisable = [ "all" ];

      # Set environment variables for glibc build
      ALTYOLO = "./build_yolo_glibc.sh";
      ALTUSER = "./build_user_glibc.sh";
      ALTLLVMLIBCOPT = " ";

      configurePhase = ''
        runHook preConfigure

        export HOME=$TMPDIR
        export HOSTNAME=nix-build

        # Skip the git-based extract_source function since we already have the source
        # The build scripts expect to be run from the repo root
        patchShebangs .

        runHook postConfigure
      '';

      buildPhase = ''
        runHook preBuild

        # Run the build script (skip tests with build_base.sh instead of build_and_test_base.sh)
        echo "Building fil-c with glibc..."
        ./build_base.sh

        runHook postBuild
      '';

      installPhase = ''
        runHook preInstall

        mkdir -p $out

        # Copy build artifacts
        cp -r build $out/build
        cp -r pizfix $out/pizfix

        # Patch ELF binaries for Nix
        for d in "$out/build/bin" "$out/pizfix/bin"; do
          if [ -d "$d" ]; then
            for exe in "$d"/*; do
              if [ -x "$exe" ] && file "$exe" | grep -q ELF; then
                patchelf --set-rpath "$out/pizfix/lib" "$exe" || true
              fi
            done
          fi
        done

        # Add Linux headers
        chmod -R u+w $out/pizfix || true
        mkdir -p $out/pizfix/os-include
        cp -r ${base.linuxHeaders}/include/. $out/pizfix/os-include/

        runHook postInstall
      '';

      # This is a large build, allow more time
      enableParallelBuilding = true;

      meta = with base.lib; {
        description = "Fil-C memory-safe C/C++ compiler (glibc edition, built from source)";
        platforms = platforms.linux;
      };
    };

    filc-clang = base.writeShellScriptBin "clang" ''
      exec ${filc-unwrapped}/build/bin/clang "$@"
    '';

    filc-clangpp = base.writeShellScriptBin "clang++" ''
      exec ${filc-unwrapped}/build/bin/clang++ "$@"
    '';

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
