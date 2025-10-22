{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    filc-src = {
      url = "tarball+https://github.com/pizlonator/fil-c/releases/download/v0.673/filc-0.673-linux-x86_64.tar.xz";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, filc-src, ... }:
  let
    system = "x86_64-linux";
    base = import nixpkgs { inherit system; };

    filc-unwrapped = base.stdenvNoCC.mkDerivation {
      pname = "filc-unwrapped";
      version = "0.673";
      src = filc-src;

      nativeBuildInputs = [ base.gnutar base.xz base.file base.patchelf ];
      dontUnpack = true;
      installPhase = ''
        mkdir -p $out
        if [ -f "$src" ]; then
          tar -xJf "$src" --strip-components=1 -C $out
        else
          cp -r "$src"/. "$out"/
        fi
        for d in "$out/build/bin/" "$out/pizfix/bin"; do
          if [ -d "$d" ]; then
            for exe in "$d"/*; do
              if [ -x "$exe" ] && file "$exe" | grep -q ELF; then
                patchelf --set-rpath "$out/pizfix/lib" "$exe" || true
              fi
            done
          fi
        done
        chmod u+w $out/pizfix
        cp -r ${base.linuxHeaders}/include $out/pizfix/os-include
      '';
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

      # at least these definitely work
      gawk = withFilC base.gawk;
      gnused = withFilC base.gnused;
      gnutar = withFilC base.gnutar;

      quickjs = withFilC base.quickjs; # slow build
      sqlite = withFilC base.sqlite;   # slow build

      bzip2 = withFilC base.bzip2;

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

      lua = (withFilC base.lua).override {
        inherit readline;
      };

      ncurses = withFilC base.ncurses;

      # tmux didn't manage to use these
      libutempter = withFilC base.libutempter;
      utf8proc = withFilC base.utf8proc;

      tmux = ((withFilC base.tmux).override {
        inherit ncurses;
        withSystemd = false;
        withUtempter = false;
        withUtf8proc = false;
      }).overrideAttrs (_: {

      });
    };
  };
}
