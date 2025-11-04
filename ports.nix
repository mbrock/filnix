# This way of doing it lets us build a bunch of specific packages
# and it's a great way to get started with applying Fil-C to nixpkgs
# but it's basically not the right way to do it.
#
# Why?  Basically because packages that do stuff like `withPackages`
# and other such recursive fixpoint kind of thingies only work
# properly when the toolchain permeates the whole system in some
# beautiful way that I don't even remotely understand.
#
# That's the problem with basing your whole system on recursive
# duck-typed fixpoint combinators!  It's literally impossible
# to understand!  Anyway I'll fix it later.
#
# See the "insane-slop" folder in this repository for a whole
# library of AI generated bullshit about how to implement the
# cross compiling toolchain and so on.  I tried it and I got
# pretty far, but then the recursive duck-typed fixpoint combinator
# threw an "infinite recursion" error and I spent a whole day
# just trying to understand where the recursion was coming from.
#
# But I'm sure I'll figure it out real soon now.
#
# Anyway it's great to start this way and just actually make sure
# that we can build and run Perl, Python, Bash, coreutils,
# and all kinds of core libraries.  We'll be happy that's
# already taken care of once we actually start doing the
# cross compilation thing.

{ base, filenv, filc-src, withFilC, fix, filcc }:

let
  # Helper to create a ported package with source + patches override
  # pkg: the nixpkgs package (e.g., base.bash, base.gnused)
  # config: { source?: { version, hash, url }, patches?, skipPatches?, deps?, attrs? }
  port = pkg: { source ? null, patches ? [], skipPatches ? [], deps ? {}, attrs ? _: {} }:
    fix pkg {
      inherit deps;
      attrs = old: 
        (if source != null then {
          inherit (source) version;
          pname = old.pname or (builtins.parseDrvName old.name).name;
          name = "${old.pname or (builtins.parseDrvName old.name).name}-${source.version}";
          src = base.fetchurl {
            url = source.url;
            hash = source.hash;
          };
        } else {}) // {
          patches = (builtins.filter
            (p: !builtins.any (skip: base.lib.hasInfix skip (builtins.toString p)) skipPatches)
            (old.patches or [])
          ) ++ patches;
        } // attrs old;
    };

  inherit (base) lib;

in rec {
  # Expose port function for external use
  inherit port;
  # Core utilities
  # bash: GNU Bourne-Again Shell
  # Deps: readline (for interactive mode), ncurses (via readline)
  # Options: interactive (enable readline), withDocs (man pages), forFHSEnv (FHS compatibility)
  bash = port base.bash {
    # source = {
    #   version = "5.2.32";
    #   hash = "sha256-0++A0rZ9jLvk0yZcY6csRvmyeOrW4OBtYYAbWPI/ULU=";
    #   url = "mirror://gnu/bash/bash-5.2.32.tar.gz";
    # };
#    patches = [./ports/patch/bash-5.2.32.patch];
    deps = { inherit readline; interactive = true; };
    attrs = old: { doCheck = false; };
  };

  bashNonInteractive = port base.bash {
    # source = {
    #   version = "5.2.32";
    #   hash = "sha256-0++A0rZ9jLvk0yZcY6csRvmyeOrW4OBtYYAbWPI/ULU=";
    #   url = "mirror://gnu/bash/bash-5.2.32.tar.gz";
    # };
#    patches = [./ports/patch/bash-5.2.32.patch];
    deps = { inherit readline; interactive = false; };
    attrs = old: { doCheck = false; };
  };

  # gnused: Stream editor for filtering/transforming text
  gnused = port base.gnused {
    source = {
      version = "4.9";
      hash = "sha256-biJrcy4c1zlGStaGK9Ghq6QteYKSLaelNRljHSSXUYE=";
      url = "https://ftpmirror.gnu.org/sed/sed-4.9.tar.xz";
    };
    patches = [./ports/patch/sed-4.9.patch];
    attrs = old: { doCheck = false; };
  };

  # acl: Access control list utilities
  # Deps: attr (extended attributes library)
  acl = port base.acl {
    deps = { inherit attr; };
  };

  # gnutar: GNU tape archiver
  # Deps: acl (for ACL support - disabled here)
  # Options: aclSupport (access control lists)
  gnutar = port base.gnutar {
    source = {
      version = "1.35";
      hash = "sha256-TWL/NzQux67XSFNTI5MMfPlKz3HDWRiCsmp+pQ8+3BY=";
      url = "https://ftpmirror.gnu.org/tar/tar-1.35.tar.xz";
    };
    patches = [./ports/patch/tar-1.35.patch];
    deps = { aclSupport = false; };
  };

  # gnugrep: GNU grep - pattern matching utility
  # Deps: pcre2 (Perl-compatible regex support)
  # Options: pcre2Support (enable -P flag for PCRE patterns)
  gnugrep = port base.gnugrep {
    source = {
      version = "3.11";
      hash = "sha256-HbKu3eidDepCsW2VKPiUyNFdrk4ZC1muzHj1qVEnbqs=";
      url = "https://ftpmirror.gnu.org/grep/grep-3.11.tar.xz";
    };
    patches = [./ports/patch/grep-3.11.patch];
    deps = { inherit pcre2; };
    attrs = old: { doCheck = false; };
  };

  # diffutils: File comparison utilities (diff, cmp, etc)
  diffutils = port base.diffutils {
    source = {
      version = "3.10";
      hash = "sha256-kOXpPMck5OvhLt6A3xY0Bjx6hVaSaFkZv+YLVWyb0J4=";
      url = "https://ftpmirror.gnu.org/diffutils/diffutils-3.10.tar.xz";
    };
    patches = [./ports/patch/diffutils-3.10.patch];
    attrs = old: { 
      doCheck = false;
      nativeBuildInputs = (old.nativeBuildInputs or []) ++ [base.perl];
      postPatch = ''
        patchShebangs man/help2man
      '';
    };
    deps = { inherit coreutils; };
  };

  # gnum4: GNU M4 macro processor (required by autotools/bison)
  gnum4 = port base.gnum4 {
    source = {
      version = "1.4.19";
      hash = "sha256-Y67eXG0zttmxNRHNC+LKwEby5w/QoHqpVzoEqCeDr5Y=";
      url = "https://ftpmirror.gnu.org/m4/m4-1.4.19.tar.xz";
    };
    patches = [./ports/patch/m4-1.4.19.patch];
  };

  m4 = gnum4;

  # Build tools
  # bison: Parser generator (yacc replacement)
  # Deps: gnum4 (required for bison)
  bison = port base.bison {
    source = {
      version = "3.8.2";
      hash = "sha256-BsnhO99+sk1M62tZIFpPZ8LH5yExGWREMP6C+9FKCrs=";
      url = "mirror://gnu/bison/bison-3.8.2.tar.gz";
    };
    patches = [./ports/patch/bison-3.8.2.patch];
    deps = { m4 = gnum4; };

    attrs = old: { 
      # test suite is slow and has 9 failures and 969 passed tests...
      doCheck = false; 
      doInstallCheck = false;
    };
  };

  # cmake: Cross-platform build system generator
  cmake = port base.cmake {
    source = {
      version = "3.30.2";
      hash = "sha256-47dznBKRw0Rz24wY4h4bGZmNpQQJaFy+6KjvKVQoZSw=";
      url = "https://cmake.org/files/v3.30/cmake-3.30.2.tar.gz";
    };
    patches = [./ports/patch/cmake-3.30.2.patch];
    attrs = old: { doCheck = false; };
  };

  runit = port base.runit {};

  # gnumake: GNU Make build tool
  # Options: guileSupport (Guile scripting - disabled here)
  gnumake = port base.gnumake {
    source = {
      version = "4.4.1";
      hash = "sha256-3Rb7HWe/q3mnL16DkHNcSePo5wtJRaFasfgd23hlj7M=";
      url = "mirror://gnu/make/make-4.4.1.tar.gz";
    };
    patches = [./ports/patch/make-4.4.1.patch];
    deps = { guileSupport = false; };
  };

  # busybox: compact userspace toolkit (init-friendly build)
  busybox = port base.busybox {
    attrs = old: {
      enableStatic = false;
      enableAppletSymlinks = false;
      enableMinimal = false;
    };
  };

  # Libraries
  # zlib: Compression library
  # Options: shared, static, splitStaticOutput
  zlib = port base.zlib {
    source = {
      version = "1.3";
      hash = "sha256-/wukwpIBPbwnUws6geH5qBPNOd4Byl4Pi/NVcC76WT4=";
      url = "https://github.com/madler/zlib/releases/download/v1.3/zlib-1.3.tar.gz";
    };
    patches = [./ports/patch/zlib-1.3.patch];
  };

  gtest = port base.gtest {
  };

  # zlib-ng: High-performance zlib replacement with optimizations
  # Deps: gtest (for tests)
  # Options: withZlibCompat (enable zlib compatibility mode)
  zlib-ng = port base.zlib-ng {
    source = {
      version = "2.2.4";
      hash = "sha256-pzNDwwk+XNxQ2Td5l8OBW4eP0RC/ZRHCx3WfKvuQ9aM=";
      url = "https://github.com/zlib-ng/zlib-ng/archive/2.2.4.tar.gz";
    };
    deps = { 
      inherit gtest;
    };
  };

  # pcre2: Perl Compatible Regular Expressions library v2
  pcre2 = port base.pcre2 {
    source = {
      version = "10.44";
      hash = "sha256-008C4RPPcZOh6/J3DTrFJwiNSF1OBH7RDl0hfG713pY=";
      url = "https://github.com/PCRE2Project/pcre2/releases/download/pcre2-10.44/pcre2-10.44.tar.bz2";
    };
  };

  # openssl: SSL/TLS cryptography library
  # Simple build avoiding nixpkgs complexity
  openssl = port (base.callPackage ./ports/openssl.nix {}) {
    deps = { inherit zlib; };
    # extract the nixpkgs base openssl patch from the nixpkgs source
    patches = [ 
      "${base.path}/pkgs/development/libraries/openssl/3.0/nix-ssl-cert-file.patch" 
    ];
  };

  # sqlite: Embedded SQL database engine
  # Deps: readline, ncurses (for interactive shell)
  # Options: interactive (enable readline in CLI)
  sqlite = port base.sqlite {
    # source = {
    #   version = "3.46.0";
    #   hash = "sha256-V5OyEuEfaWh2p/iNckCAyRZGcpPHko35TiNYI/3Qn64=";
    #   url = "https://sqlite.org/2024/sqlite-autoconf-3460000.tar.gz";
    # };
    # patches = [./ports/patch/sqlite.patch];
    deps = { inherit readline ncurses; interactive = true; };
    attrs = old: { doCheck = false; };
  };

  # libpng: PNG image format library
  # Deps: zlib
  # Options: apngSupport (animated PNG)
  libpng = port base.libpng {
    source = {
      version = "1.6.43";
      hash = "sha256-Uw5O1JHsI91X2FYBy3XTVbUzDN9Vae7JkNn2Yw7W9tI=";
      url = "mirror://sourceforge/libpng/libpng-1.6.43.tar.xz";
    };
    patches = [./ports/patch/libpng-1.6.43.patch];
    deps = { inherit zlib; };
  };

  # expat: XML parser library
  expat = port base.expat {
    source = {
      version = "2.7.1";
      hash = "sha256-NUVSVEuPmQEuUGL31XDsd/FLQSo/9cfY0NrmLA0hfDA=";
      url = "https://github.com/libexpat/libexpat/releases/download/R_2_7_1/expat-2.7.1.tar.xz";
    };
    patches = [./ports/patch/expat-2.7.1.patch];
  };

  # libxml2: GNOME XML library
  libxml2 = port base.libxml2 {
    source = {
      version = "2.14.4";
      hash = "sha256-9ZOMFpDJ3RPvKFrSm17cqjcGCh/J8rTOcPYr1ZKZEH4=";
      url = "https://download.gnome.org/sources/libxml2/2.14/libxml2-2.14.4.tar.xz";
    };
    patches = [./ports/patch/libxml2-2.14.4.patch];
    attrs = old: { doCheck = false; };
  };

  # libffi: Foreign function interface library
  libffi = port base.libffi {
    source = {
      version = "3.4.6";
      hash = "sha256-sN6p3yPIY6elDoJUQPPr/6vWXfFJcQjl1Dd0eEOJWk4=";
      url = "https://github.com/libffi/libffi/releases/download/v3.4.6/libffi-3.4.6.tar.gz";
    };
    patches = [./ports/patch/libffi-3.4.6.patch];
    attrs = old: {
      configureFlags = [
        "--with-gcc-arch=native"
        "--disable-static"
        "--disable-exec-static-tramp"
      ];
      doCheck = false;
    };
  };

  # libarchive: Multi-format archive/compression library
  # Deps: zlib, openssl
  libarchive = port base.libarchive {
    source = {
      version = "3.7.4";
      hash = "sha256-t1y0XMXN9hfxCv2O0HdJBX4k2iLSxqFzfSn/zFXnYZo=";
      url = "https://github.com/libarchive/libarchive/releases/download/v3.7.4/libarchive-3.7.4.tar.xz";
    };
    patches = [./ports/patch/libarchive-3.7.4.patch];
    deps = { inherit zlib openssl; };
    attrs = old: { doCheck = false; };
  };

  # ncurses: Terminal handling library
  # Options: abiVersion, enableStatic, mouseSupport, unicodeSupport, withCxx, withTermlib
  ncurses = port base.ncurses {
  };

  # readline: Command-line editing library
  # Deps: ncurses
  readline = port base.readline {
    deps = { inherit ncurses; };
  };

  # libevent: Event notification library
  # Options: sslSupport
  libevent = port base.libevent {
    deps = { inherit openssl; };
    source = {
      version = "2.1.12";
      hash = "sha256-kubeG+nsF2Qo/SNnZ35hzv/C7hyxGQNQN6J9NGsEA7s=";
      url = "https://github.com/libevent/libevent/releases/download/release-2.1.12-stable/libevent-2.1.12-stable.tar.gz";
    };
    patches = [./ports/patch/libevent-2.1.12.patch];
  };

  libutempter = port base.libutempter {
    deps = { 
      # doesn't seem to actually need it; will fix glib later
      glib = null;
    };
  };

  utf8proc = port base.utf8proc {};

  # Terminal/system tools
  # tmux: Terminal multiplexer
  # Deps: ncurses, libevent
  # Options: withSystemd, withUtf8proc
  tmux = port base.tmux {
    deps = { 
      inherit ncurses libevent libutempter utf8proc;
      withSystemd = false; 
    };
  };


  # Languages
  # lua: Lightweight embeddable scripting language
  # Deps: readline (command-line editing)
  lua = 
    filenv.mkDerivation rec {
      pname = "lua";
      version = "5.4.7";
      src = base.fetchurl {
        url = "https://www.lua.org/ftp/lua-5.4.7.tar.gz";
        sha256 = "sha256-n79eKO+GxphY9tPTTszDLpEcGii0Eg/z6EqqcM+/HjA=";
      };

      nativeBuildInputs = [filcc];

      makeFlags = [
        "CC=${filcc}/bin/clang"
        "INSTALL_TOP=${placeholder "out"}"
        "INSTALL_MAN=${placeholder "out"}/share/man/man1"
        "R=${version}"
      ];

      buildInputs = [ncurses readline];

      postPatch = ''
        sed -i "s@#define LUA_ROOT[[:space:]]*\"/usr/local/\"@#define LUA_ROOT  \"$out/\"@g" \
          src/luaconf.h
        grep $out src/luaconf.h
      '';

      passthru = {
        pkgs = {
          isLuaJIT = false;
          # fine, I give up
        };
        withPackages = f: lua;
        luaOnBuild = lua;
      };
    };

  # perl: Practical Extraction and Report Language
  # Deps: zlib
  perl = port base.perl {
    source = {
      version = "5.40.0";
      hash = "sha256-x0A0jzVzljJ6l5XT6DI7r9D+ilx4NfwcuroMyN/nFh8=";
      url = "https://www.cpan.org/src/5.0/perl-5.40.0.tar.gz";
    };
    patches = [./ports/patch/perl-5.40.0.patch];
    deps = { inherit zlib; };
    attrs = old: { doCheck = false; };
  };

  # NOT YET WORKING!
  #
  # Something's wrong with either "frozen modules" or "perf bootstrap"
  # or something else.
  #
  # python3: Python programming language
  # Deps: openssl (SSL/TLS), zlib, readline, sqlite (for sqlite3 module), expat (XML), libffi (ctypes)
  # Options: mimetypesSupport, enableOptimizations, stripBytecode, stripTests, bluezSupport, x11Support
  python3 = port base.python3 {
    source = {
      version = "3.12.5";
      hash = "sha256-+oouEsXmILCfU+ZbzYdVDS5aHi4Ev4upkdzFUROHY5c=";
      url = "https://www.python.org/ftp/python/3.12.5/Python-3.12.5.tar.xz";
    };
    patches = [./ports/patch/Python-3.12.5.patch];
    deps = { 
      inherit openssl zlib readline sqlite expat libffi; 
      mimetypesSupport = true;
      enableLTO = false;
    };
    attrs = old: { 
      doCheck = false;
      preConfigure = ''
        export NIX_CFLAGS_COMPILE="''${NIX_CFLAGS_COMPILE//-Wa,--compress-debug-sections/}"
      '';
      configureFlags = old.configureFlags ++ [
      ];
      nativeBuildInputs = with base; [
        base.python3 
        autoreconfHook
        autoconf
        automake libtool autoconf-archive
        m4
        pkg-config
      ];
    };
  };

  # Version control
  # git: Distributed version control system
  # Deps: openssl, zlib, pcre2 (for PCRE regex in grep)
  # Options: withManual (docs), perlSupport, pythonSupport, sendEmailSupport, svnSupport
  git = port base.git {
    source = {
      version = "2.46.0";
      hash = "sha256-fxI0YqKLfKPr4mB0hfcWhVTCsQ38FVx+xGMAZmrCf5U=";
      url = "https://www.kernel.org/pub/software/scm/git/git-2.46.0.tar.xz";
    };
    skipPatches = ["git-send-email-honor-PATH.patch"];
    patches = [./ports/patch/git-2.46.0.patch];
    deps = { 
      inherit openssl pcre2 curl expat;
      withManual = false; 
      perlSupport = false;
      pythonSupport = false; 
      sendEmailSupport = false; 
      zlib-ng = zlib;
    };
    attrs = old: {
      doCheck = false;
      doInstallCheck = false; # some failures? kinda slow
      makeFlags = base.lib.filter (p: p != "ZLIB_NG=1") old.makeFlags;
    };
  };

  # Text processing
  # gettext: Internationalization/localization tools
  gettext = port base.gettext {
    source = {
      version = "0.22.5";
      hash = "sha256-7BcFselpuDqfBzFE7IBhUduIEn9eQP5alMtsj6SJlqA=";
      url = "mirror://gnu/gettext/gettext-0.22.5.tar.gz";
    };
    patches = [./ports/patch/gettext-0.22.5.patch];
    attrs = old: { doCheck = false; };
  };

  # texinfo: GNU documentation system
  texinfo = port base.texinfo {
    source = {
      version = "7.1";
      hash = "sha256-TsI+QWG/eKC4ecfz0UeOsKdpj1j4NZKvNW20jw8AiLU=";
      url = "mirror://gnu/texinfo/texinfo-7.1.tar.xz";
    };
    patches = [./ports/patch/texinfo-7.1.patch];
    attrs = old: { doCheck = false; };
  };

  # absolutely doesn't work
  luajit = port base.luajit {
    deps = {
      enableJIT = false;
      enableFFI = false;

      # weird quasi-crosscompiling single step fuckery
      buildPackages = filenv // { stdenv = filenv; };
    };
  };

  unibilium = port base.unibilium {
    deps = {
      inherit ncurses;
    };
  };

  tree-sitter = port base.tree-sitter {
    deps = {
      inherit (base) installShellFiles;
    };
  };

  # The Lua package stuff seems really difficult to do
  # without turning Fil-C into an actual cross platform?
  #
  # So this doesn't work.
  neovim = port base.neovim-unwrapped {
    deps = {
      inherit libuv utf8proc tree-sitter;
      lua = lua;
    };
  };

  # emacs: Extensible, customizable text editor
  emacs = port base.emacs {
    source = {
      version = "30.1";
      hash = "sha256-eTWjpRgLXbA9OQZnbrWPIHPcbj/QYkv58I3IWx5lCIQ=";
      url = "https://git.savannah.gnu.org/cgit/emacs.git/snapshot/emacs-30.1.tar.gz";
    };
    patches = [./ports/patch/emacs-30.1.patch];
    attrs = old: { doCheck = false; };
  };

  # Network
  # openssh: OpenSSH secure shell client/server
  openssh = port base.openssh {
    source = {
      version = "9.8p1";
      hash = "sha256-6pz8/fR51/K/SWKjKSrKNEAiEaUQwOjW6Pf+YY4j3to=";
      url = "mirror://openbsd/OpenSSH/portable/openssh-9.8p1.tar.gz";
    };
    patches = [./ports/patch/openssh-9.8p1.patch];
    attrs = old: { doCheck = false; };
  };

  # curl: Command-line tool for transferring data with URLs
  # Note: nixpkgs defines curl as curlMinimal.override, so we do the same
  # to get a proper package with .override support
  # Deps: openssl, zlib, brotli, nghttp2, libidn2, libssh2, libpsl, zstd
  # Options: Multiple protocol/feature support flags (see query-package.sh curl)
  curl = port base.curlMinimal {
    deps = {
      inherit openssl zlib brotli nghttp2 libidn2 libpsl zstd libkrb5;
      idnSupport = true;
      pslSupport = true;
      zstdSupport = true;
      brotliSupport = true;
      scpSupport = false;
    };
    attrs = old: { doCheck = false; };
  };

  # Compression
  # xz: LZMA compression utilities
  xz = port base.xz {
    source = {
      version = "5.6.2";
      hash = "sha256-qds7s9ZOJIoPrpY/j7a6hRomuhgi5QTcDv0YqAxibK8=";
      url = "https://github.com/tukaani-project/xz/releases/download/v5.6.2/xz-5.6.2.tar.xz";
    };
    patches = [./ports/patch/xz-5.6.2.patch];
    attrs = old: {
      nativeBuildInputs = (old.nativeBuildInputs or []) ++ (with base; [
        automake116x autoconf
      ]);
      doCheck = false; # one failing test thwarted by Fil-C
    };
  };

  # zstd: Zstandard compression algorithm
  zstd = port base.zstd {
    patches = [./ports/patch/zstd-1.5.6.patch];
    deps = { inherit bashNonInteractive; };
    attrs = old: {
      # Disable assembly for Fil-C compatibility
      # CMake doesn't have a ZSTD_NO_ASM option, so we pass the flag directly
      cmakeFlags = (old.cmakeFlags or []) ++ [
        "-DCMAKE_C_FLAGS=-DZSTD_DISABLE_ASM"
      ];

      # playTests do a filc panic
      doCheck = false;
    };
  };

  # Shells
  # dash: POSIX-compliant shell (lightweight alternative to bash)
  dash = port base.dash {
    source = {
      version = "0.5.12";
      hash = "sha256-akdKxG6LCzKRbExg32lMggWNMpfYs4W3RQgDDKSo8oo=";
      url = "http://gondor.apana.org.au/~herbert/dash/files/dash-0.5.12.tar.gz";
    };
    patches = [./ports/patch/dash-0.5.12.patch];
    deps = { inherit libedit; };
  };

  # Additional libraries
  # attr: Extended attribute support library
  attr = port base.attr {
    source = {
      version = "2.5.2";
      hash = "sha256-qKRTtGN4ZZLgcmyGPQFRQ5gSMWj/1dC2qdNuXe1qWoE=";
      url = "mirror://savannah/attr/attr-2.5.2.tar.gz";
    };
    patches = [./ports/patch/attr-2.5.2.patch];
  };

  # libxcrypt: Modern password hashing library
  libxcrypt = port base.libxcrypt {
    source = {
      version = "4.4.36";
      hash = "sha256-u5rcIKZFCKuVSDAN/cIDJCi/OYLbnwx7PYAiEWqxfGw=";
      url = "https://github.com/besser82/libxcrypt/releases/download/v4.4.36/libxcrypt-4.4.36.tar.xz";
    };
    patches = [./ports/patch/libxcrypt-4.4.36.patch];
  };

  # libuv: Cross-platform async I/O library
  libuv = port base.libuv {
    source = {
      version = "1.48.0";
      hash = "sha256-fx24rDaNidG68WO6wepf5RIGl6c5EMiuay//s1UdWfs=";
      url = "https://dist.libuv.org/dist/v1.48.0/libuv-v1.48.0.tar.gz";
    };
    patches = [./ports/patch/libuv-v1.48.0.patch];
  };

  # Network protocol libraries (for curl and others)
  # krb5: Kerberos network authentication protocol
  # Deps: openssl, keyutils, libedit
  # Options: withLdap, withLibedit, withVerto
  libkrb5 = port base.libkrb5 {
    source = {
      version = "1.21.3";
      hash = "sha256-t6TNXq1n+wi5gLIavRUP9yF+heoyDJ7QxtrdMEhArTU=";
      url = "https://kerberos.org/dist/krb5/1.21/krb5-1.21.3.tar.gz";
    };
    patches = [./ports/patch/krb5-1.21.3.patch];
    deps = { inherit openssl keyutils libedit; };
    attrs = old: {
      patchFlags = ["-p2"];
    };
  };

  # brotli: Generic lossless compression algorithm
  brotli = port base.brotli {
  };

  # nghttp2: HTTP/2 C library
  # Deps: c-ares, libev, zlib, openssl
  # Options: enableApp, enableHttp3, enableJemalloc, enablePython
  nghttp2 = port base.nghttp2 {
    deps = { 
      inherit zlib openssl; 
#      c-aresMinimal = c-ares;
    };
    attrs = old: {
      nativeBuildInputs = [
        depizloing-nm
      ] ++ (old.nativeBuildInputs or []);

      configureFlags = [
        "--disable-app"
      ];

      # don't warn about -Wdeprecated-literal-operator
      NIX_CFLAGS_COMPILE = "-Wno-deprecated-literal-operator";
    };
  };

  nghttp3 = port base.nghttp3 {
  };

  # Doesn't work, needs QuicTLS instead of OpenSSL.
  # Porting Fil-C's OpenSSL patch to QuicTLS is probably easy?
  ngtcp2 = port base.ngtcp2 {
    deps = {
      inherit brotli libev nghttp3 openssl;
    };
  };

  # libidn2: Internationalized domain names (IDNA2008/TR46) library
  # Note: nixpkgs wraps libidn2 in no-bootstrap-reference.nix which removes .override
  # so we call the package directly to get the unwrapped version
  # Deps: libunistring
  libidn2 = port (base.callPackage "${base.path}/pkgs/development/libraries/libidn2" {}) {
    deps = { inherit libunistring; };
  };

  depizloing-nm = base.writeShellScriptBin "nm" ''
    ${filcc}/bin/nm "$@" | sed 's/\bpizlonated_//g'
  '';

  # libssh2: SSH2 client-side library
  # Deps: zlib, openssl
  libssh2 = port base.libssh2 {
    deps = { inherit zlib openssl; };
    attrs = old: {
      nativeBuildInputs = 
        [
          depizloing-nm
          base.pkg-config
        ] ++ (old.nativeBuildInputs or []);
      doCheck = false;
      configureFlags = [
        # examples don't link properly with Fil-C toolchain
        "--disable-examples-build"
      ] ++ (old.configureFlags or []);
    };
  };

  # libpsl: Public Suffix List library
  # Deps: libidn2, libunistring
  libpsl = port base.libpsl {
    deps = { inherit libidn2 libunistring; };
  };

  # Supporting libraries
  # libunistring: Unicode string library
  libunistring = port base.libunistring {
  };

  # c-ares: Asynchronous DNS resolver library
  c-ares = port base.c-aresMinimal {
  };

  # libev: Event loop library
  libev = port base.libev {
  };

  # keyutils: Linux key management utilities
  keyutils = port base.keyutils {
    source = {
      version = "1.6.3";
      hash = "sha256-ph1XBhNq5MBb1I+GGGvP29iN2L1RB+Phlckkz8Gzm7Q=";
      url = "https://git.kernel.org/pub/scm/linux/kernel/git/dhowells/keyutils.git/snapshot/keyutils-1.6.3.tar.gz";
    };
    skipPatches = ["after_eq"]; # our patch does this already
    patches = [./ports/patch/keyutils-1.6.3.patch];
  };

  # libedit: BSD line editing library
  # Deps: ncurses
  libedit = port base.libedit {
    source = {
      version = "20240808-3.1";
      hash = "sha256-XwVzNJ13xKSJZxkc3WY03Xql9jmMalf+A3zAJpbWCZ8=";
      url = "https://thrysoee.dk/editline/libedit-20240808-3.1.tar.gz";
    };
    patches = [./ports/patch/libedit-20240808-3.1.patch];
    deps = { inherit ncurses; };
  };

  # Advanced packages
  # quickjs: Small embeddable JavaScript engine
  quickjs = port base.quickjs {
    source = {
      version = "2024-02-14";
      hash = "sha256-PEv4+JW/pUvrSGyNEhgRJ3Hs/FrDvhA2hR70FWghLgM=";
      url = "https://bellard.org/quickjs/quickjs-2024-01-13.tar.xz";
    };
    patches = [./ports/patch/quickjs.patch];
    attrs = old: { doCheck = false; };
  };

  # tcl: Tool Command Language scripting language
  tcl = port base.tcl {
  };

  # System utilities
  # coreutils: GNU core utilities (ls, cp, mv, etc)
  # Deps: gmp (for extended precision in numfmt)
  # Options: withOpenssl, withPrefix, singleBinary
  coreutils = port base.coreutils {
    deps = { inherit gmp; };
    attrs = old: { doCheck = false; };
  };

  # gmp: GNU Multiple Precision Arithmetic Library
  gmp = port base.gmp {
    attrs = old: { doCheck = false; };
  };

  # gawk: GNU AWK text processing language
  gawk = port base.gawk {
    attrs = old: { doCheck = false; };
  };

  # bzip2: Compression utility
  bzip2 = port base.bzip2 {
  };

  # which: Shows full path of commands
  which = port base.which {
  };

  # file: File type identification utility
  file = port base.file {
    attrs = old: { doCheck = false; };
    deps = { inherit zlib; };
  };

  # nano: Pico clone text editor
  # Deps: ncurses
  nano = port base.nano {
    deps = { inherit ncurses; };
  };

  # nethack: Classic roguelike dungeon exploration game
  # Deps: ncurses
  nethack = port base.nethack {
    deps = { inherit ncurses; };
  };

  # wasm3: Fast WebAssembly interpreter
  # Built from upstream source (not a nixpkgs port)
  wasm3 = base.callPackage ./wasm3.nix {
    stdenv = filenv;
  };

  # kitty-doom: Memory-safe DOOM for terminal
  # Built from upstream source (not a nixpkgs port)
  kitty-doom = base.callPackage ./kitty-doom.nix {
    stdenv = filenv;
  };

  lesspipe = port base.lesspipe {
    deps = { inherit perl bash; };
  };

  figlet = port base.figlet {};
  clolcat = port base.clolcat {};

  flex = port base.flex {
    deps = { inherit bison m4; };
  };

  bc = port base.bc {
    deps = { inherit readline flex; };
  };

  ed = port base.ed { 
    deps = { runtimeShellPackage = bash; }; 
  };

  autoconf = port base.autoconf {
    deps = { inherit m4; };
  };

  automake = port base.automake {
    deps = { inherit autoconf; };
  };

  oniguruma = port base.oniguruma {
  };

  libiconv = lib.getDev filcc.libc;

  pkgconf-unwrapped = port base.pkgconf-unwrapped {
    attrs = old: { 
      nativeBuildInputs = (old.nativeBuildInputs or []) ++ [depizloing-nm];
      enableParallelBuilding = true;
    };
  };

  pkgconf = base.callPackage (base.path + "/pkgs/build-support/pkg-config-wrapper") {
    pkg-config = pkgconf-unwrapped;
    baseBinName = "pkgconf";
  };

  libtool = port base.libtool {
    deps = { inherit m4 file; };
  };

  jq = port base.jq {
    deps = { inherit oniguruma; };
  };
}
