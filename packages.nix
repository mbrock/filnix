# Sample packages built with Fil-C
# This is a catalog of packages we're testing with Fil-C
{ base, filenv, filc-src, withFilC, fix,
  kitty-doom-src, doom1-wad, puredoom-h,
  wasm3-src
}:

rec {
  # Some easy ones to get started!
  gawk = fix base.gawk {} (old: {
    enableParallelBuilding = true;
  });
  gnused = fix base.gnused {} (old: {
    enableParallelBuilding = true;
  });
  gnutar = fix base.gnutar {} (old: {
    enableParallelBuilding = true;
  });
  bzip2 = fix base.bzip2 {} (old: {
    enableParallelBuilding = true;
  });
  gnugrep = fix base.gnugrep {
    inherit pcre2;
  } (old: {
    doCheck = false;
    enableParallelBuilding = true;
  });

  readline = fix base.readline {
    inherit ncurses;
  } (old: {});

  # Nethack works!
  nethack = fix base.nethack {
    inherit ncurses;
  } (old: {});

  # Memory-safe DOOM for your Kitty/Ghostty terminal
  kitty-doom = filenv.mkDerivation {
    pname = "kitty-doom";
    version = "git";
    src = kitty-doom-src;

    nativeBuildInputs = [ base.curl base.makeWrapper ];

    preBuild = ''
      cp ${doom1-wad} DOOM1.WAD
      cp ${puredoom-h} src/PureDOOM.h
      chmod +w src/PureDOOM.h
      
      # Fix Carmack's 1993 allocator to use 8-byte alignment instead of 4-byte
      substituteInPlace src/PureDOOM.h \
        --replace-fail '(size + 3) & ~3' '(size + 7) & ~7'
    '';

    installPhase = ''
      mkdir -p $out/bin $out/share/kitty-doom
      cp build/kitty-doom $out/share/kitty-doom/
      cp DOOM1.WAD $out/share/kitty-doom/
      ln -s DOOM1.WAD $out/share/kitty-doom/doom1.wad
      
      makeWrapper $out/share/kitty-doom/kitty-doom $out/bin/kitty-doom \
        --set DOOMWADDIR $out/share/kitty-doom
    '';

    meta = {
      homepage = "https://github.com/jserv/kitty-doom";
      description = "Play DOOM in modern terminals with Kitty Graphics Protocol";
    };
  };

  lua = fix base.lua {
    inherit readline;
  } (old: {});

  coreutils = fix base.coreutils {
    inherit gmp;
  } (old: {
    doCheck = false;
  });

  gmp = fix base.gmp {} (old: {
    doCheck = false;
  });

  bash = fix base.bash {
    inherit readline;
  } (old: {
    patches = (old.patches or []) ++ [
      ./patches/bash-5.2.32-filc.patch
    ];
  });

  libsodium = fix base.libsodium {} (old: {
    hardeningDisable = ["stackprotector"];
    configureFlags = [ "--disable-ssp" ];
    separateDebugInfo = false;
    doCheck = false;
  });

  gflags = fix base.gflags {} (old: {});

  quickjs = fix base.quickjs {} (old: {}); # slow build
  sqlite = fix base.sqlite {} (old: {});   # slow build

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
    inherit zlib;
  } {};

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

  pcre2 = fix base.pcre2 {} (old: {
    enableParallelBuilding = true;
  });
  which = fix base.which {} (old: {});
  file = fix base.file {} (old: {});
  libxml2 = fix base.libxml2 {} (old: {
    enableParallelBuilding = true;
    doCheck = false;
  });

  ncurses = fix base.ncurses {} (old: {});
  libutempter = fix base.libutempter {} (old: {});
  utf8proc = fix base.utf8proc {} (old: {});
  libevent = fix base.libevent {
    sslSupport = false;
  } (old: {});

  nano = fix base.nano {
    inherit ncurses;
  } (old: {});

  tmux = fix base.tmux {
    inherit ncurses libevent libutempter utf8proc;
    withSystemd = false;
  } (old: {});

  gtest = fix base.gtest {} (old: {});

  zlib = fix base.zlib {} (old: {});
  zlib-ng = fix base.zlib-ng 
    { inherit gtest; }
    (old: {
      cmakeFlags = old.cmakeFlags ++ [ "-DZLIB_ENABLE_TESTS=OFF" ];
      outputs = ["out" "dev"];
      nativeBuildInputs = old.nativeBuildInputs or [] ++ [base.breakpointHook];
    });

  libtool = fix base.libtool {} (old: {});

  graphviz = fix base.graphviz {} (old: {
    buildInputs = [];
    nativeBuildInputs = with base; [
     libtool autoreconfHook  autoconf python3 bison flex pkg-config
    ];
    configureFlags = [
      "--without-x"
      "--disable-ltdl"
    ];
    doCheck = false;
  });

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
  libjpeg = fix base.libjpeg {} (old: {
    doCheck = false;
  });
}
