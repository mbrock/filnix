# Sample packages built with Fil-C
# This is a catalog of packages we're testing with Fil-C
{ base, filenv, filc-src, withFilC, fix,
  wasm3-src
}:

let
  extras = {
    kitty-doom = base.callPackage ./kitty-doom.nix {};
  };
in

rec {
  # Some easy ones to get started!
  gawk = fix base.gawk {
    attrs = old: {
      enableParallelBuilding = true;
    };
  };
  gnused = fix base.gnused {
    attrs = old: {
      enableParallelBuilding = true;
    };
  };
  gnutar = fix base.gnutar {
    attrs = old: {
      enableParallelBuilding = true;
    };
  };
  bzip2 = fix base.bzip2 {
    attrs = old: {
      enableParallelBuilding = true;
    };
  };
  gnugrep = fix base.gnugrep {
    deps = { inherit pcre2; };
    attrs = old: {
      doCheck = false;
      enableParallelBuilding = true;
    };
  };

  readline = fix base.readline {
    deps = { inherit ncurses; };
  };

  # Nethack works!
  nethack = fix base.nethack {
    deps = { inherit ncurses; };
  };

  # Memory-safe DOOM for your Kitty/Ghostty terminal
  kitty-doom = fix extras.kitty-doom {};

  lua = fix base.lua {
    deps = { inherit readline; };
  };

  coreutils = fix base.coreutils {
    deps = { inherit gmp; };
    attrs = old: {
      doCheck = false;
    };
  };

  gmp = fix base.gmp {
    attrs = old: {
      doCheck = false;
    };
  };

  bash = fix base.bash {
    deps = { inherit readline; };
    attrs = old: {
      patches = (old.patches or []) ++ [
        ./patches/bash-5.2.32-filc.patch
      ];
    };
  };

  libsodium = fix base.libsodium {
    attrs = old: {
      hardeningDisable = ["stackprotector"];
      configureFlags = [ "--disable-ssp" ];
      separateDebugInfo = false;
      doCheck = false;
    };
  };

  gflags = fix base.gflags {};

  quickjs = fix base.quickjs {}; # slow build
  sqlite = fix base.sqlite {};   # slow build

  wasm3 =
    filenv.mkDerivation {
      src = wasm3-src;
      pname = "wasm3";
      version = "0.5.1";
      enableParallelBuilding = true;
      nativeBuildInputs = with base; [
        cmake ninja
      ];
      cmakeFlags = ["-DBUILD_WASI=simple"];
    };

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

  openssl = fix base.openssl {
    deps = { inherit zlib; };
  };

  # openssl = 
  #   filenv.mkDerivation (final: {
  #     src = "${filc-src}/projects/openssl-${final.version}";
  #     pname = "openssl";
  #     version = "3.3.1";
  #     enableParallelBuilding = true;
  #     nativeBuildInputs = with base; [perl];
  #     buildInputs = [zlib];
  #     configurePhase = ''
  #       ./Configure zlib --prefix=$out --libdir=$out/lib
  #     '';
  #     patchPhase = ''
  #       patchShebangs .
  #     '';
  #     buildPhase = "make -j$NIX_BUILD_CORES && make -j$NIX_BUILD_CORES libcrypto.so";
  #     installPhase = ''
  #       make -j$NIX_BUILD_CORES install_sw
  #       make -j$NIX_BUILD_CORES install_ssldirs
  #     '';
  #   });

  pcre2 = fix base.pcre2 {
    attrs = old: {
      enableParallelBuilding = true;
    };
  };
  which = fix base.which {};
  file = fix base.file {};
  libxml2 = fix base.libxml2 {
    attrs = old: {
      enableParallelBuilding = true;
      doCheck = false;
    };
  };

  ncurses = fix base.ncurses {};
  libutempter = fix base.libutempter {};
  utf8proc = fix base.utf8proc {};
  libevent = fix base.libevent {
    deps = { sslSupport = false; };
  };

  nano = fix base.nano {
    deps = { inherit ncurses; };
  };

  tmux = fix base.tmux {
    deps = {
      inherit ncurses libevent libutempter utf8proc;
      withSystemd = false;
    };
  };

  gtest = fix base.gtest {};

  zlib = fix base.zlib {};
  zlib-ng = fix base.zlib-ng {
    deps = { inherit gtest; };
    attrs = old: {
      cmakeFlags = old.cmakeFlags ++ [ "-DZLIB_ENABLE_TESTS=OFF" ];
      outputs = ["out" "dev"];
      nativeBuildInputs = old.nativeBuildInputs or [] ++ [base.breakpointHook];
    };
  };

  libtool = fix base.libtool {};

  graphviz = fix base.graphviz {
    attrs = old: {
      buildInputs = [];
      nativeBuildInputs = with base; [
       libtool autoreconfHook  autoconf python3 bison flex pkg-config
      ];
      configureFlags = [
        "--without-x"
        "--disable-ltdl"
      ];
      doCheck = false;
    };
  };

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
  libjpeg = fix base.libjpeg {
    attrs = old: {
      doCheck = false;
    };
  };
}
