# Ported packages from upstream fil-c with patches
# Based on ports/patches.nix
# See nixpkgs-package-info.nix for package metadata (args, versions)
{ base, filenv, filc-src, withFilC, fix, wasm3-src ? null, kitty-doom-src ? null, doom1-wad ? null, puredoom-h ? null }:

let
  # Helper to create a ported package with source + patches override
  # pkg: the nixpkgs package (e.g., base.bash, base.gnused)
  # config: { source?: { version, hash, url }, patches?, deps?, attrs? }
  port = pkg: { source ? null, patches ? [], deps ? {}, attrs ? _: {} }:
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
          patches = (old.patches or []) ++ patches;
        } // attrs old;
    };

in rec {
  # Core utilities
  # bash: GNU Bourne-Again Shell
  # Deps: readline (for interactive mode), ncurses (via readline)
  # Options: interactive (enable readline), withDocs (man pages), forFHSEnv (FHS compatibility)
  bash = port base.bash {
    source = {
      version = "5.2.32";
      hash = "sha256-1b1593ffea2155ccc27cbee01754680b37c23dacae11d315f1cb===";
      url = "mirror://gnu/bash/bash-5.2.tar.gz";
    };
    patches = [./ports/patch/bash-5.2.32.patch];
    deps = { inherit readline; interactive = true; };
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
    deps = { inherit pcre2; pcre2Support = true; };
  };

  # diffutils: File comparison utilities (diff, cmp, etc)
  diffutils = port base.diffutils {
    source = {
      version = "3.10";
      hash = "sha256-90DxXb6Tlz5N5M0r8W8scXd6Of0bYKJiqIPLbkrNENo=";
      url = "https://ftpmirror.gnu.org/diffutils/diffutils-3.10.tar.xz";
    };
    patches = [./ports/patch/diffutils-3.10.patch];
    attrs = old: { doCheck = false; };
  };

  # gnum4: GNU M4 macro processor (required by autotools/bison)
  gnum4 = port base.gnum4 {
    source = {
      version = "1.4.19";
      hash = "sha256-2ytc9acOLqS2cgSaAYa6Oi+PNgNhArSH3yv7o4H2W6E=";
      url = "https://ftpmirror.gnu.org/m4/m4-1.4.19.tar.xz";
    };
    patches = [./ports/patch/m4-1.4.19.patch];
  };

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
    deps = { inherit gnum4; };
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

  # zlib-ng: High-performance zlib replacement with optimizations
  # Deps: gtest (for tests)
  # Options: withZlibCompat (enable zlib compatibility mode)
  zlib-ng = port base.zlib-ng {
    source = {
      version = "2.2.4";
      hash = "sha256-Khmrhp5qy4vvoQe4WgoogpjWrgcUB/q8zZeqIydthYg=";
      url = "https://github.com/zlib-ng/zlib-ng/archive/2.2.4.tar.gz";
    };
    deps = { };
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
  # Deps: zlib (compression support)
  openssl = port base.openssl {
    source = {
      version = "3.3.1";
      hash = "sha256-d3zVlihMiDN1oqehG/XSeG/FQTJV76sgxQ1v/m0CC34=";
      url = "https://www.openssl.org/source/openssl-3.3.1.tar.gz";
    };
    patches = [./ports/patch/openssl-3.3.1.patch];
    deps = { inherit zlib; };
    attrs = old: { doCheck = false; };
  };

  # sqlite: Embedded SQL database engine
  # Deps: readline, ncurses (for interactive shell)
  # Options: interactive (enable readline in CLI)
  sqlite = port base.sqlite {
    source = {
      version = "3.46.0";
      hash = "sha256-V5OyEuEfaWh2p/iNckCAyRZGcpPHko35TiNYI/3Qn64=";
      url = "https://sqlite.org/2024/sqlite-autoconf-3460000.tar.gz";
    };
    patches = [./ports/patch/sqlite.patch];
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
      hash = "sha256-vUfJHkbB3kCLEVZ5LQFV0fFrTMt6BQF1YlHaNd4UwY4=";
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
      hash = "sha256-IBnRw/OmKMIr2iTy3kHdy7MOLre+tlpv1NWwO/vgVOo=";
      url = "https://github.com/libffi/libffi/releases/download/v3.4.6/libffi-3.4.6.tar.gz";
    };
    patches = [./ports/patch/libffi-3.4.6.patch];
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
    source = {
      version = "6.5";
      hash = "sha256-KCz/iK7V/3IZeg21cSvqT7p1KNV5yvjOrgVpkbVYG9k=";
      url = "mirror://gnu/ncurses/ncurses-6.5.tar.gz";
    };
  };

  # readline: Command-line editing library
  # Deps: ncurses
  readline = port base.readline {
    source = {
      version = "8.3p1";
      hash = "sha256-hIMUtmrB9NGRLL3rJXVZFpxzPxYoJbIHcMGKHFPkDU0=";
      url = "mirror://gnu/readline/readline-8.3.tar.gz";
    };
    deps = { inherit ncurses; };
  };

  # libevent: Event notification library
  # Options: sslSupport
  libevent = port base.libevent {
    source = {
      version = "2.1.12";
      hash = "sha256-BRp15w/ZTfvMU5gefZbQsppdwWQ/SP0SJSMnOh6EaGI=";
      url = "https://github.com/libevent/libevent/releases/download/release-2.1.12-stable/libevent-2.1.12-stable.tar.gz";
    };
    patches = [./ports/patch/libevent-2.1.12.patch];
  };

  # Terminal/system tools
  # tmux: Terminal multiplexer
  # Deps: ncurses, libevent
  # Options: withSystemd, withUtf8proc
  tmux = port base.tmux {
    deps = { inherit ncurses libevent; withSystemd = false; };
  };

  # Languages
  # lua: Lightweight embeddable scripting language
  # Deps: readline (command-line editing)
  lua = port base.lua {
    source = {
      version = "5.4.7";
      hash = "sha256-AMvaREzhX+KlAkkqmTI6pPaXdpL/3qnPQFXpvAHFLhw=";
      url = "https://www.lua.org/ftp/lua-5.4.7.tar.gz";
    };
    patches = [./ports/patch/lua-5.4.7.patch];
    deps = { inherit readline; };
  };

  # perl: Practical Extraction and Report Language
  # Deps: zlib
  perl = port base.perl {
    source = {
      version = "5.40.0";
      hash = "sha256-dvXxSz5SqnOaZsb5fPQ6Ic0XB+gDDLN/oCu4qVyU/sA=";
      url = "https://www.cpan.org/src/5.0/perl-5.40.0.tar.gz";
    };
    patches = [./ports/patch/perl-5.40.0.patch];
    deps = { inherit zlib; };
    attrs = old: { doCheck = false; };
  };

  # python3: Python programming language
  # Deps: openssl (SSL/TLS), zlib, readline, sqlite (for sqlite3 module), expat (XML), libffi (ctypes)
  # Options: mimetypesSupport, enableOptimizations, stripBytecode, stripTests, bluezSupport, x11Support
  python3 = port base.python3 {
    source = {
      version = "3.12.5";
      hash = "sha256-XnxUJE2YuGSKGW7LWLtqGKEXWxvyexCvu3JW5GFiH5I=";
      url = "https://www.python.org/ftp/python/3.12.5/Python-3.12.5.tar.xz";
    };
    patches = [./ports/patch/Python-3.12.5.patch];
    deps = { inherit openssl zlib readline sqlite expat libffi; mimetypesSupport = true; };
    attrs = old: { doCheck = false; };
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
    deps = { inherit openssl pcre2 zlib-ng; withManual = false; perlSupport = false; pythonSupport = false; sendEmailSupport = false; };
    attrs = old: {
      doCheck = false;
      # Filter out the git-send-email-honor-PATH.patch (fails on 2.46.0) but keep other nixpkgs patches
      patches = (builtins.filter
        (p: !(base.lib.hasSuffix "git-send-email-honor-PATH.patch" (builtins.toString p)))
        (old.patches or [])
      ) ++ [./ports/patch/git-2.46.0.patch];
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

  # Editors
  # vim: Vi IMproved text editor
  vim = port base.vim {
    source = {
      version = "9.1.0660";
      hash = "sha256-z31cH73oQ1ejVcGtIBGMiUfV4WhOcaZzVJ8eljX5v+c=";
      url = "https://github.com/vim/vim/archive/v9.1.0660.tar.gz";
    };
    patches = [./ports/patch/vim-9.1.0660.patch];
    attrs = old: { doCheck = false; };
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

  # Compression
  # xz: LZMA compression utilities
  xz = port base.xz {
    source = {
      version = "5.6.2";
      hash = "sha256-xaImRVTfxSKZlasvkH1Kr+sJAVThUL2698bRbbR5hp4=";
      url = "https://github.com/tukaani-project/xz/releases/download/v5.6.2/xz-5.6.2.tar.xz";
    };
    patches = [./ports/patch/xz-5.6.2.patch];
  };

  # zstd: Zstandard compression algorithm
  zstd = port base.zstd {
    source = {
      version = "1.5.6";
      hash = "sha256-IcmH9cBaI+Q/+7ZH/irwW98YhVuAkKAR0CCIHnkNJ+8=";
      url = "https://github.com/facebook/zstd/releases/download/v1.5.6/zstd-1.5.6.tar.gz";
    };
    patches = [./ports/patch/zstd-1.5.6.patch];
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
      hash = "sha256-7RBwuLfLGvDJCsb6xNVpe9pL7OL7AKWa0u5M1DLcpAs=";
      url = "https://dist.libuv.org/dist/v1.48.0/libuv-v1.48.0.tar.gz";
    };
    patches = [./ports/patch/libuv-v1.48.0.patch];
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
    source = {
      version = "8.6.15";
      hash = "sha256-0cE7jdrlCEbhGE4hqc93QKz/xoFXeKY1Yf7kD6hfN/s=";
      url = "mirror://sourceforge/tcl/tcl8.6.15-src.tar.gz";
    };
    patches = [./ports/patch/tcl-8.6.15.patch];
  };

  # System utilities
  # coreutils: GNU core utilities (ls, cp, mv, etc)
  # Deps: gmp (for extended precision in numfmt)
  # Options: withOpenssl, withPrefix, singleBinary
  coreutils = port base.coreutils {
    source = {
      version = "9.5";
      hash = "sha256-yydpOzN6oENEgTHPjGISYJZfZQ+nZvnzU0dGh4mz7yg=";
      url = "mirror://gnu/coreutils/coreutils-9.5.tar.xz";
    };
    deps = { inherit gmp; };
    attrs = old: { doCheck = false; };
  };

  # gmp: GNU Multiple Precision Arithmetic Library
  gmp = port base.gmp {
    source = {
      version = "6.3.0";
      hash = "sha256-+yizkHZcF27d1/MrHKq4KEUCWbvhhPrCNECp+nZn7c8=";
      url = "mirror://gnu/gmp/gmp-6.3.0.tar.xz";
    };
    attrs = old: { doCheck = false; };
  };

  # gawk: GNU AWK text processing language
  gawk = port base.gawk {
    source = {
      version = "5.3.0";
      hash = "sha256-+djHlVe05Z9KkMn7tD5sFwJSqwNzrYmDJSGkfDJJZhY=";
      url = "mirror://gnu/gawk/gawk-5.3.0.tar.xz";
    };
    attrs = old: { doCheck = false; };
  };

  # bzip2: Compression utility
  bzip2 = port base.bzip2 {
    source = {
      version = "1.0.8";
      hash = "sha256-q1jst6TzEN9cwP14qCCJPj5urwZ6l2Lrvgky/t+16hw=";
      url = "https://sourceware.org/pub/bzip2/bzip2-1.0.8.tar.gz";
    };
  };

  # which: Shows full path of commands
  which = port base.which {
    source = {
      version = "2.21";
      hash = "sha256-0yqBfi5n1YCQQ7nOILLevS7kx7Y5bLc5F3S1ggJSQd8=";
      url = "mirror://gnu/which/which-2.21.tar.gz";
    };
  };

  # file: File type identification utility
  file = port base.file {
    source = {
      version = "5.45";
      hash = "sha256-Z7V+cG11V+PyHkh23S+fGVk9AB1OdvTZwDWgM7xYvZU=";
      url = "https://astron.com/pub/file/file-5.45.tar.gz";
    };
    attrs = old: { doCheck = false; };
  };

  # nano: Pico clone text editor
  # Deps: ncurses
  nano = port base.nano {
    source = {
      version = "8.2";
      hash = "sha256-HFB+d/AAPMF2R32tG4vTRn6v/YbtbJmJQj0GCiouaI8=";
      url = "mirror://gnu/nano/nano-8.2.tar.xz";
    };
    deps = { inherit ncurses; };
  };

  # nethack: Classic roguelike dungeon exploration game
  # Deps: ncurses
  nethack = port base.nethack {
    source = {
      version = "3.6.7";
      hash = "sha256-QER9NNOKzj7R1gq5X7NCGd+Nj13eZEo0COlBBYpK8bI=";
      url = "https://nethack.org/download/3.6.7/nethack-367-src.tgz";
    };
    deps = { inherit ncurses; };
  };

  # wasm3: Fast WebAssembly interpreter
  # Built from upstream source (not a nixpkgs port)
  wasm3 = assert wasm3-src != null; filenv.mkDerivation {
    src = wasm3-src;
    pname = "wasm3";
    version = "0.5.1";
    enableParallelBuilding = true;
    nativeBuildInputs = with base; [ cmake ninja ];
    cmakeFlags = ["-DBUILD_WASI=simple"];
  };

  # kitty-doom: Memory-safe DOOM for terminal
  # Built from upstream source (not a nixpkgs port)
  kitty-doom = assert kitty-doom-src != null && doom1-wad != null && puredoom-h != null;
    filenv.mkDerivation {
      src = kitty-doom-src;
      pname = "kitty-doom";
      version = "0.1.0";
      enableParallelBuilding = true;

      nativeBuildInputs = with base; [ pkg-config ];

      preBuild = ''
        cp ${puredoom-h} PureDOOM.h
        cp ${doom1-wad} doom1.wad
      '';

      installPhase = ''
        mkdir -p $out/bin $out/share/doom
        cp kitty-doom $out/bin/
        cp doom1.wad $out/share/doom/
      '';
    };
}
