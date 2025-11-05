{
  base,
  filenv,
  filc-src,
  withFilC,
  fix,
  filcc,
}:
let
  DSL = import ./portconf.nix { inherit lib fix base; };
  inherit (DSL)
    buildPort
    arg
    use
    src
    skipTests
    skipCheck
    parallelize
    tool
    link
    patch
    skipPatch
    removeCFlag
    addCFlag
    configure
    wip
    ;
  inherit (DSL) github gnu gnuTarGz;
  inherit (base) lib;

  port = buildPort;
in
rec {
  zlib = port [
    base.zlib
    (src "1.3" (github "madler/zlib" (
      v: "v${v}/zlib-${v}.tar.gz"
    )) "sha256-/wukwpIBPbwnUws6geH5qBPNOd4Byl4Pi/NVcC76WT4=")
    (patch ./ports/patch/zlib-1.3.patch)
  ];

  openssl = port [
    (base.callPackage ./ports/openssl.nix { })
    { inherit zlib; }
    (patch (
      "${base.path}/pkgs/development/libraries"
      + "/openssl/3.0/nix-ssl-cert-file.patch"
    ))
  ];

  libevent = port [
    base.libevent
    { inherit openssl; }
    (src "2.1.12" (github "libevent/libevent" (
      v: "release-${v}-stable/libevent-${v}-stable.tar.gz"
    )) "sha256-kubeG+nsF2Qo/SNnZ35hzv/C7hyxGQNQN6J9NGsEA7s=")
    (patch ./ports/patch/libevent-2.1.12.patch)
  ];

  ncurses = port [ base.ncurses ];

  utf8proc = port [ base.utf8proc ];

  libutempter = port [
    base.libutempter
    { glib = null; }
  ];

  tmux = port [
    base.tmux
    { inherit ncurses; }
    { inherit libevent; }
    { inherit libutempter; }
    { inherit utf8proc; }
    { withSystemd = false; }
  ];

  inherit filcc;

  depizloing-nm = base.writeShellScriptBin "nm" ''
    ${filcc}/bin/nm "$@" | sed 's/\bpizlonated_//g'
  '';

  # Work in progress (alphabetically sorted)
  acl = port [
    base.acl
    { inherit attr; }
  ];

  attr = port [
    base.attr
    (src "2.5.2" (
      v: "mirror://savannah/attr/attr-${v}.tar.gz"
    ) "sha256-qKRTtGN4ZZLgcmyGPQFRQ5gSMWj/1dC2qdNuXe1qWoE=")
    (patch ./ports/patch/attr-2.5.2.patch)
  ];

  autoconf = port [
    base.autoconf
    { inherit m4; }
  ];

  automake = port [
    base.automake
    { inherit autoconf; }
  ];

  bash = port [
    base.bash
    {
      inherit readline;
      interactive = true;
    }
    skipCheck
  ];

  bashNonInteractive = port [
    base.bash
    {
      inherit readline;
      interactive = false;
    }
    skipCheck
  ];

  bc = port [
    base.bc
    { inherit readline flex; }
  ];

  bison = port [
    base.bison
    (src "3.8.2" (gnu "bison")
      "sha256-m7oCFMz38QecXVkhAEUie89hlRmEDr+oDNOEnP9aW/I="
    )
    (patch ./ports/patch/bison-3.8.2.patch)
    { m4 = gnum4; }
    skipTests
  ];

  brotli = port [ base.brotli ];

  busybox = port [
    base.busybox
    (use {
      enableStatic = false;
      enableAppletSymlinks = false;
      enableMinimal = false;
    })
  ];

  bzip2 = port [ base.bzip2 ];

  c-ares = port [ base.c-aresMinimal ];

  clolcat = port [ base.clolcat ];

  cmake = port [
    base.cmake
    (src "3.30.2" (
      v: "https://cmake.org/files/v3.30/cmake-${v}.tar.gz"
    ) "sha256-47dznBKRw0Rz24wY4h4bGZmNpQQJaFy+6KjvKVQoZSw=")
    (patch ./ports/patch/cmake-3.30.2.patch)
    skipCheck
  ];

  coreutils = port [
    base.coreutils
    { inherit gmp; }
    skipCheck
  ];

  curl = port [
    base.curlMinimal
    { inherit openssl; }
    { inherit zlib; }
    { inherit brotli; }
    { inherit nghttp2; }
    { inherit libidn2; }
    { inherit libpsl; }
    { inherit zstd; }
    { inherit libkrb5; }
    { idnSupport = true; }
    { pslSupport = true; }
    { zstdSupport = true; }
    { brotliSupport = true; }
    { scpSupport = false; }
    skipCheck
  ];

  dash = port [
    base.dash
    (src "0.5.12" (
      v: "http://gondor.apana.org.au/~herbert/dash/files/dash-${v}.tar.gz"
    ) "sha256-akdKxG6LCzKRbExg32lMggWNMpfYs4W3RQgDDKSo8oo=")
    (patch ./ports/patch/dash-0.5.12.patch)
    { inherit libedit; }
  ];

  db4 = db48;

  db48 = port [ base.db48 ];

  diffutils = port [
    base.diffutils
    (src "3.10" (gnu "diffutils")
      "sha256-kOXpPMck5OvhLt6A3xY0Bjx6hVaSaFkZv+YLVWyb0J4="
    )
    (patch ./ports/patch/diffutils-3.10.patch)
    { inherit coreutils; }
    (tool base.perl)
    (use { postPatch = "patchShebangs man/help2man"; })
    skipCheck
  ];

  ed = port [
    base.ed
    { runtimeShellPackage = bash; }
  ];

  emacs = port [
    base.emacs
    (src "30.1" (
      v: "https://git.savannah.gnu.org/cgit/emacs.git/snapshot/emacs-${v}.tar.gz"
    ) "sha256-eTWjpRgLXbA9OQZnbrWPIHPcbj/QYkv58I3IWx5lCIQ=")
    (patch ./ports/patch/emacs-30.1.patch)
    skipCheck
  ];

  expat = port [
    base.expat
    (src "2.7.1" (github "libexpat/libexpat" (
      v: "R_${builtins.replaceStrings [ "." ] [ "_" ] v}/expat-${v}.tar.xz"
    )) "sha256-NUVSVEuPmQEuUGL31XDsd/FLQSo/9cfY0NrmLA0hfDA=")
    (patch ./ports/patch/expat-2.7.1.patch)
  ];

  figlet = port [ base.figlet ];

  file = port [
    base.file
    { inherit zlib; }
    skipCheck
  ];

  flex = port [
    base.flex
    { inherit bison m4; }
  ];

  git = port [
    base.git
    (src "2.46.0" (
      v: "https://www.kernel.org/pub/software/scm/git/git-${v}.tar.xz"
    ) "sha256-fxI0YqKLfKPr4mB0hfcWhVTCsQ38FVx+xGMAZmrCf5U=")
    (skipPatch "git-send-email-honor-PATH.patch")
    (patch ./ports/patch/git-2.46.0.patch)
    { inherit openssl; }
    { inherit pcre2; }
    { inherit curl; }
    { inherit expat; }
    { withManual = false; }
    { perlSupport = false; }
    { pythonSupport = false; }
    { sendEmailSupport = false; }
    { zlib-ng = zlib; }
    skipTests
    (use (old: {
      makeFlags = base.lib.filter (p: p != "ZLIB_NG=1") old.makeFlags;
    }))
  ];

  gawk = port [
    base.gawk
    skipCheck
  ];

  gmp = port [
    base.gmp
    skipCheck
  ];

  gnugrep = port [
    base.gnugrep
    (src "3.11" (gnu "grep") "sha256-HbKu3eidDepCsW2VKPiUyNFdrk4ZC1muzHj1qVEnbqs=")
    (patch ./ports/patch/grep-3.11.patch)
    { inherit pcre2; }
    skipCheck
  ];

  gnumake = port [
    base.gnumake
    (src "4.4.1" (gnuTarGz "make")
      "sha256-3Rb7HWe/q3mnL16DkHNcSePo5wtJRaFasfgd23hlj7M="
    )
    (patch ./ports/patch/make-4.4.1.patch)
    { guileSupport = false; }
  ];

  gnused = port [
    base.gnused
    (src "4.9" (gnu "sed") "sha256-biJrcy4c1zlGStaGK9Ghq6QteYKSLaelNRljHSSXUYE=")
    (patch ./ports/patch/sed-4.9.patch)
    skipCheck
  ];

  gnutar = port [
    base.gnutar
    (src "1.35" (gnu "tar") "sha256-TWL/NzQux67XSFNTI5MMfPlKz3HDWRiCsmp+pQ8+3BY=")
    (patch ./ports/patch/tar-1.35.patch)
    { aclSupport = false; }
  ];

  gnum4 = port [
    base.gnum4
    (src "1.4.19" (gnu "m4") "sha256-Y67eXG0zttmxNRHNC+LKwEby5w/QoHqpVzoEqCeDr5Y=")
    (patch ./ports/patch/m4-1.4.19.patch)
  ];

  gtest = port [ base.gtest ];

  jq = port [
    base.jq
    { inherit oniguruma; }
  ];

  keyutils = port [
    base.keyutils
    (src "1.6.3" (
      v:
      "https://git.kernel.org/pub/scm/linux/kernel/git/dhowells/keyutils.git/snapshot/keyutils-${v}.tar.gz"
    ) "sha256-ph1XBhNq5MBb1I+GGGvP29iN2L1RB+Phlckkz8Gzm7Q=")
    (patch ./ports/patch/keyutils-1.6.3.patch)
    (skipPatch "after_eq")
  ];

  lesspipe = port [
    base.lesspipe
    { inherit perl; }
    { inherit bash; }
  ];

  libarchive = port [
    base.libarchive
    (src "3.7.4" (github "libarchive/libarchive" (
      v: "v${v}/libarchive-${v}.tar.xz"
    )) "sha256-t1y0XMXN9hfxCv2O0HdJBX4k2iLSxqFzfSn/zFXnYZo=")
    (patch ./ports/patch/libarchive-3.7.4.patch)
    { inherit zlib; }
    { inherit openssl; }
    skipCheck
  ];

  libedit = port [
    base.libedit
    (src "20240808-3.1" (
      v: "https://thrysoee.dk/editline/libedit-${v}.tar.gz"
    ) "sha256-XwVzNJ13xKSJZxkc3WY03Xql9jmMalf+A3zAJpbWCZ8=")
    (patch ./ports/patch/libedit-20240808-3.1.patch)
    { inherit ncurses; }
  ];

  libev = port [ base.libev ];

  libffi = port [
    base.libffi
    (src "3.4.6" (github "libffi/libffi" (
      v: "v${v}/libffi-${v}.tar.gz"
    )) "sha256-sN6p3yPIY6elDoJUQPPr/6vWXfFJcQjl1Dd0eEOJWk4=")
    (patch ./ports/patch/libffi-3.4.6.patch)
    skipCheck
    (configure "--with-gcc-arch=native")
    (configure "--disable-static")
    (configure "--disable-exec-static-tramp")
  ];

  libiconv = lib.getDev filcc.libc;

  libidn2 = port [
    (base.callPackage "${base.path}/pkgs/development/libraries/libidn2" { })
    { inherit libunistring; }
  ];

  libkrb5 = port [
    base.libkrb5
    (src "1.21.3" (
      v: "https://kerberos.org/dist/krb5/1.21/krb5-${v}.tar.gz"
    ) "sha256-t6TNXq1n+wi5gLIavRUP9yF+heoyDJ7QxtrdMEhArTU=")
    (patch ./ports/patch/krb5-1.21.3.patch)
    { inherit openssl; }
    { inherit keyutils; }
    { inherit libedit; }
    (use { patchFlags = [ "-p2" ]; })
  ];

  libpng = port [
    base.libpng
    (src "1.6.43" (
      v: "mirror://sourceforge/libpng/libpng-${v}.tar.xz"
    ) "sha256-Uw5O1JHsI91X2FYBy3XTVbUzDN9Vae7JkNn2Yw7W9tI=")
    (patch ./ports/patch/libpng-1.6.43.patch)
    { inherit zlib; }
  ];

  libpsl = port [
    base.libpsl
    { inherit libidn2; }
    { inherit libunistring; }
  ];

  libssh2 = port [
    base.libssh2
    { inherit zlib; }
    { inherit openssl; }
    (tool depizloing-nm)
    (tool base.pkg-config)
    skipCheck
    (configure "--disable-examples-build")
  ];

  libtool = port [
    base.libtool
    { inherit m4; }
    { inherit file; }
  ];

  libunistring = port [ base.libunistring ];

  libuuid = util-linux;

  libuv = port [
    base.libuv
    (src "1.48.0" (
      v: "https://dist.libuv.org/dist/v${v}/libuv-v${v}.tar.gz"
    ) "sha256-fx24rDaNidG68WO6wepf5RIGl6c5EMiuay//s1UdWfs=")
    (patch ./ports/patch/libuv-v1.48.0.patch)
  ];

  libxcrypt = port [
    base.libxcrypt
    (src "4.4.36" (github "besser82/libxcrypt" (
      v: "v${v}/libxcrypt-${v}.tar.xz"
    )) "sha256-5eH0yu4KAd4q7ibjE4gH1tPKK45nKHlm0f79ZeH9iUM=")
    (patch ./ports/patch/libxcrypt-4.4.36.patch)
    (tool depizloing-nm)
    skipCheck
  ];

  libxml2 = port [
    base.libxml2
    (patch ./ports/patch/libxml2-2.14.4.patch)
    { inherit zlib; }
    { inherit ncurses; }
    { pythonSupport = false; }
    skipCheck
  ];

  lighttpd = port [
    base.lighttpd
    (patch ./lighttpd-filc.patch)
    { inherit openssl; }
    { inherit pcre2; }
    { inherit libxml2; }
    { inherit sqlite; }
    { inherit libuuid; }
    { inherit zlib; }
    { inherit bzip2; }
    { inherit which; }
    { inherit file; }
    { lua5_1 = lua; }
    { linux-pam = pam; }
    { enableMagnet = true; }
    { enableWebDAV = true; }
    { enablePam = true; }
    (tool depizloing-nm)
    skipCheck
    (link brotli)
    (link zstd)
    (link libkrb5)
    (configure "--with-zlib")
    (configure "--with-bzip2")
    (configure "--with-brotli")
    (configure "--with-zstd")
    (configure "--with-krb5")
  ];

  lua = base.callPackage ./ports/lua.nix {
    inherit
      filenv
      filcc
      ncurses
      readline
      base
      ;
  };

  m4 = gnum4;

  nano = port [
    base.nano
    { inherit ncurses; }
  ];

  nethack = port [
    base.nethack
    { inherit ncurses; }
  ];

  ngtcp2 = port [
    base.ngtcp2
    { inherit brotli; }
    { inherit libev; }
    { inherit nghttp3; }
    { inherit openssl; }
  ];

  nghttp2 = port [
    base.nghttp2
    { inherit zlib; }
    { inherit openssl; }
    (tool depizloing-nm)
    (configure "--disable-app")
    (addCFlag "-Wno-deprecated-literal-operator")
  ];

  nghttp3 = port [ base.nghttp3 ];

  oniguruma = port [ base.oniguruma ];

  openssh = port [
    base.openssh
    (src "9.8p1" (
      v: "mirror://openbsd/OpenSSH/portable/openssh-${v}.tar.gz"
    ) "sha256-6pz8/fR51/K/SWKjKSrKNEAiEaUQwOjW6Pf+YY4j3to=")
    (patch ./ports/patch/openssh-9.8p1.patch)
    skipCheck
  ];

  pam = port [
    base.linux-pam
    { inherit libxcrypt db4; }
    (tool depizloing-nm)
    skipCheck
  ];

  pcre2 = port [
    base.pcre2
    (src "10.44" (github "PCRE2Project/pcre2" (
      v: "pcre2-${v}/pcre2-${v}.tar.bz2"
    )) "sha256-008C4RPPcZOh6/J3DTrFJwiNSF1OBH7RDl0hfG713pY=")
  ];

  perl = port [
    base.perl
    (src "5.40.0" (
      v: "https://www.cpan.org/src/5.0/perl-${v}.tar.gz"
    ) "sha256-x0A0jzVzljJ6l5XT6DI7r9D+ilx4NfwcuroMyN/nFh8=")
    (patch ./ports/patch/perl-5.40.0.patch)
    { inherit zlib; }
    skipCheck
  ];

  pkgconf-unwrapped = port [
    base.pkgconf-unwrapped
    (tool depizloing-nm)
    parallelize
  ];

  pkgconf =
    base.callPackage (base.path + "/pkgs/build-support/pkg-config-wrapper")
      {
        pkg-config = pkgconf-unwrapped;
        baseBinName = "pkgconf";
      };

  python3 = port [
    base.python3
    (src "3.12.5" (
      v: "https://www.python.org/ftp/python/${v}/Python-${v}.tar.xz"
    ) "sha256-+oouEsXmILCfU+ZbzYdVDS5aHi4Ev4upkdzFUROHY5c=")
    (patch ./ports/patch/Python-3.12.5.patch)
    { inherit openssl; }
    { inherit zlib; }
    { inherit readline; }
    { inherit sqlite; }
    { inherit expat; }
    { inherit libffi; }
    { mimetypesSupport = true; }
    { enableLTO = false; }
    skipCheck
    (tool base.python3)
    (tool base.autoreconfHook)
    (tool base.autoconf)
    (tool base.automake)
    (tool base.libtool)
    (tool base.autoconf-archive)
    (tool base.m4)
    (tool base.pkg-config)
    (removeCFlag "-Wa,--compress-debug-sections")
  ];

  quickjs = port [
    base.quickjs
    (src "2024-02-14" (
      v: "https://bellard.org/quickjs/quickjs-2024-01-13.tar.xz"
    ) "sha256-PEv4+JW/pUvrSGyNEhgRJ3Hs/FrDvhA2hR70FWghLgM=")
    (patch ./ports/patch/quickjs.patch)
    skipCheck
  ];

  readline = port [
    base.readline
    { inherit ncurses; }
  ];

  runit = port [ base.runit ];

  sqlite = port [
    base.sqlite
    { inherit readline; }
    { inherit ncurses; }
    { interactive = true; }
    skipCheck
    (removeCFlag "-DSQLITE_ENABLE_STMT_SCANSTATUS")
  ];

  tcl = port [ base.tcl ];

  tree-sitter = port [
    base.tree-sitter
    { inherit (base) installShellFiles; }
  ];

  unibilium = port [
    base.unibilium
    { inherit ncurses; }
  ];

  util-linux = port [
    base.util-linux
    { inherit zlib; }
    { inherit sqlite; }
    { inherit pam; }
    { inherit libxcrypt; }
    { capabilitiesSupport = false; }
    { cryptsetupSupport = false; }
    { nlsSupport = false; }
    { ncursesSupport = false; }
    { pamSupport = true; }
    { shadowSupport = true; }
    { systemdSupport = false; }
    { translateManpages = false; }
    (tool depizloing-nm)
    parallelize
  ];

  which = port [ base.which ];

  xz = port [
    base.xz
    (src "5.6.2" (github "tukaani-project/xz" (
      v: "v${v}/xz-${v}.tar.xz"
    )) "sha256-qds7s9ZOJIoPrpY/j7a6hRomuhgi5QTcDv0YqAxibK8=")
    (patch ./ports/patch/xz-5.6.2.patch)
    (tool base.automake116x)
    (tool base.autoconf)
    skipCheck
  ];

  zlib-ng = port [
    base.zlib-ng
    (src "2.2.4" (github "zlib-ng/zlib-ng" (
      v: "${v}.tar.gz"
    )) "sha256-pzNDwwk+XNxQ2Td5l8OBW4eP0RC/ZRHCx3WfKvuQ9aM=")
    { inherit gtest; }
  ];

  zstd = port [
    base.zstd
    (patch ./ports/patch/zstd-1.5.6.patch)
    { inherit bashNonInteractive; }
    skipCheck
    (addCFlag "-DZSTD_DISABLE_ASM")
  ];

  wasm3 = port [
    (base.callPackage ./wasm3.nix { })
  ];

  kittydoom = port [
    (base.callPackage ./kitty-doom.nix { })
  ];
}
