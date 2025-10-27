# Sample packages built with Fil-C
# This is a catalog of packages we're testing with Fil-C
{ base, filenv, filc-src, withFilC, parallelize, dontTest, debug,
  kitty-doom-src }:

rec {
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

  # Memory-safe DOOM for your Kitty/Ghostty terminal
  kitty-doom = filenv.mkDerivation {
    pname = "kitty-doom";
    version = "git";
    src = kitty-doom-src;

    installPhase = ''
      mkdir -p $out/bin
      cp build/kitty-doom $out/bin/
    '';

    meta = {
      homepage = "https://github.com/jserv/kitty-doom";
      description = "Play DOOM in modern terminals with Kitty Graphics Protocol";
    };
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

  libsodium = withFilC (base.libsodium.overrideAttrs (_: {
    hardeningDisable = ["stackprotector"];
    configureFlags = [ "--disable-ssp" ];
    separateDebugInfo = false;
    doCheck = false;
  }));

  gflags = withFilC base.gflags;

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
      buildPhase = "make -j$NIX_BUILD_CORES && make -j$NIX_BUILD_CORES libcrypto.so";
      installPhase = ''
        make -j$NIX_BUILD_CORES install_sw
        make -j$NIX_BUILD_CORES install_ssldirs
      '';
    });

  pcre2 = (parallelize (withFilC base.pcre2));
  which = withFilC base.which;
  file = withFilC base.file;
  libxml2 = dontTest (parallelize (withFilC base.libxml2));

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

  gtest = withFilC base.gtest;

  zlib = withFilC base.zlib;
  zlib-ng =( debug ((withFilC base.zlib-ng).override {
    inherit gtest;
  })).overrideAttrs (old: {
    cmakeFlags = old.cmakeFlags ++ [ "-DZLIB_ENABLE_TESTS=OFF" ];
    outputs = ["out" "dev"];
  });

  libtool = withFilC base.libtool;

  graphviz = ((withFilC base.graphviz).overrideAttrs (_: {
    buildInputs = [bash libtool];
    nativeBuildInputs = with base; [
      autoreconfHook  autoconf python3 bison flex pkg-config
    ];
    configureFlags = [
      "--without-x"
      "--disable-ltdl"
    ];
    doCheck = false;
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
}
