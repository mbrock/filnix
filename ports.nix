{
  pkgs,
  filenv,
  filc-src,
  withFilC,
  fix,
  filcc,
}:
let
  DSL = import ./portconf.nix { inherit lib fix pkgs; };
  inherit (DSL)
    buildPort
    arg
    use
    src
    skipTests
    skipCheck
    parallelize
    serialize
    tranquilize
    tool
    link
    patch
    skipPatch
    removeCFlag
    addCFlag
    removeCMakeFlag
    addCMakeFlag
    configure
    wip
    ;
  inherit (DSL) github gnu gnuTarGz;
  inherit (pkgs) lib;

  port = buildPort;
in
rec {
  zlib = port [
    pkgs.zlib
    (src "1.3" (github "madler/zlib" (
      v: "v${v}/zlib-${v}.tar.gz"
    )) "sha256-/wukwpIBPbwnUws6geH5qBPNOd4Byl4Pi/NVcC76WT4=")
    (patch ./ports/patch/zlib-1.3.patch)

    tranquilize # perl needs zlib
  ];

  openssl = port [
    (pkgs.callPackage ./ports/openssl.nix { })
    { inherit zlib; }
    (patch ("${pkgs.path}/pkgs/development/libraries" + "/openssl/3.0/nix-ssl-cert-file.patch"))
  ];

  libevent = port [
    pkgs.libevent
    { inherit openssl; }
    (src "2.1.12" (github "libevent/libevent" (
      v: "release-${v}-stable/libevent-${v}-stable.tar.gz"
    )) "sha256-kubeG+nsF2Qo/SNnZ35hzv/C7hyxGQNQN6J9NGsEA7s=")
    (patch ./ports/patch/libevent-2.1.12.patch)
  ];

  ncurses = port [ pkgs.ncurses ];

  utf8proc = port [ pkgs.utf8proc ];

  libutempter = port [
    pkgs.libutempter
    { glib = null; }
  ];

  tmux = port [
    pkgs.tmux
    { inherit ncurses; }
    { inherit libevent; }
    { inherit libutempter; }
    { inherit utf8proc; }
    { withSystemd = false; }
  ];

  inherit filcc;

  depizloing-nm = pkgs.writeShellScriptBin "nm" ''
    ${filcc}/bin/nm "$@" | sed 's/\bpizlonated_//g'
  '';

  # Work in progress (alphabetically sorted)
  acl = port [
    pkgs.acl
    { inherit attr; }
  ];

  attr = port [
    pkgs.attr
    (src "2.5.2" (
      v: "mirror://savannah/attr/attr-${v}.tar.gz"
    ) "sha256-Ob9nRS+kHQlIwhl2AQU/SLPXigYTiXNDMqYwmmgMbIc=")
    (patch ./ports/patch/attr-2.5.2.patch)
  ];

  autoconf = port [
    pkgs.autoconf
    { inherit m4; }
  ];

  automake = port [
    pkgs.automake
    { inherit autoconf; }
  ];

  bash = port [
    pkgs.bash
    {
      inherit readline;
      interactive = true;
    }
    skipCheck
  ];

  bashNonInteractive = port [
    pkgs.bash
    {
      inherit readline;
      interactive = false;
    }
    skipCheck
  ];

  bc = port [
    pkgs.bc
    { inherit readline flex; }
  ];

  bison = port [
    pkgs.bison
    (src "3.8.2" (gnu "bison") "sha256-m7oCFMz38QecXVkhAEUie89hlRmEDr+oDNOEnP9aW/I=")
    (patch ./ports/patch/bison-3.8.2.patch)
    { m4 = gnum4; }
    skipTests
  ];

  brotli = port [ pkgs.brotli ];

  busybox = port [
    pkgs.busybox
    (use {
      enableStatic = false;
      enableAppletSymlinks = false;
      enableMinimal = false;
    })
  ];

  bzip2 = port [ pkgs.bzip2 ];

  c-ares = port [ pkgs.c-aresMinimal ];

  clolcat = port [ pkgs.clolcat ];

  cmake = port [
    pkgs.cmake
    {
      inherit
        bzip2
        expat
        libarchive
        xz
        zlib
        libuv
        openssl
        ;
      curlMinimal = curl;
      rhash = pkgs.rhash; # not ported yet
    }
    (src "3.30.2" (
      v: "https://cmake.org/files/v3.30/cmake-${v}.tar.gz"
    ) "sha256-47dznBKRw0Rz24wY4h4bGZmNpQQJaFy+6KjvKVQoZSw=")
    (patch ./ports/patch/cmake-3.30.2.patch)
    skipCheck
  ];

  coreutils = port [
    pkgs.coreutils
    { inherit gmp; }
    skipCheck
  ];

  curl = port [
    pkgs.curlMinimal
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
    pkgs.dash
    (src "0.5.12" (
      v: "http://gondor.apana.org.au/~herbert/dash/files/dash-${v}.tar.gz"
    ) "sha256-akdKxG6LCzKRbExg32lMggWNMpfYs4W3RQgDDKSo8oo=")
    (patch ./ports/patch/dash-0.5.12.patch)
    { inherit libedit; }
  ];

  db4 = db48;

  db48 = port [ pkgs.db48 ];

  diffutils = port [
    pkgs.diffutils
    (src "3.10" (gnu "diffutils") "sha256-kOXpPMck5OvhLt6A3xY0Bjx6hVaSaFkZv+YLVWyb0J4=")
    (patch ./ports/patch/diffutils-3.10.patch)
    { inherit coreutils; }
    (tool pkgs.perl)
    (use { postPatch = "patchShebangs man/help2man"; })
    skipCheck
  ];

  ed = port [
    pkgs.ed
    { runtimeShellPackage = bash; }
  ];

  emacs = port [
    pkgs.emacs
    {
      inherit ncurses zlib libxml2;
      # Disable TLS for now (gnutls has too many deps)
      gnutls = null;
      # Minimal terminal-only Emacs - disable everything we can
      withX = false;
      withGTK3 = false;
      withXwidgets = false;
      withNS = false;
      withPgtk = false;
      withImageMagick = false;
      withWebP = false;
      withTreeSitter = false;
      withSQLite3 = false;
      withGpm = false;
      withSelinux = false;
      withSystemd = false;
      withAcl = false;
      withMailutils = false;
      withNativeCompilation = false;
      withCsrc = false;
      withCairo = false;
      withAthena = false;
      withMotif = false;
      withDbus = false;
      withAlsaLib = false;
      withGlibNetworking = false;
      withXinput2 = false;
      withJansson = false;
    }
    (src "30.1" (
      v: "https://git.savannah.gnu.org/cgit/emacs.git/snapshot/emacs-${v}.tar.gz"
    ) "sha256-5PJeGhy7/LMfqIxckfwohs/Up+Eip+uWcNPsSm+BCEs=")
    (patch ./ports/patch/emacs-30.1.patch)
    (configure "--with-gnutls=ifavailable")
    (configure "--with-dumping=none")
    (configure "--with-pdumper=no")
    (configure "--with-unexec=no")
    skipCheck
  ];

  expat = port [
    pkgs.expat
    (src "2.7.1" (github "libexpat/libexpat" (
      v: "R_${builtins.replaceStrings [ "." ] [ "_" ] v}/expat-${v}.tar.xz"
    )) "sha256-NUVSVEuPmQEuUGL31XDsd/FLQSo/9cfY0NrmLA0hfDA=")
    (patch ./ports/patch/expat-2.7.1.patch)
  ];

  figlet = port [ pkgs.figlet ];

  file = port [
    pkgs.file
    { inherit zlib; }
    skipCheck
  ];

  findutils = port [
    pkgs.findutils
    { inherit coreutils; }
  ];

  flex = port [
    pkgs.flex
    { inherit bison m4; }
  ];

  git = port [
    pkgs.git
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
      makeFlags = pkgs.lib.filter (p: p != "ZLIB_NG=1") old.makeFlags;
    }))
  ];

  gawk = port [
    pkgs.gawk
    skipCheck
  ];

  gmp = port [
    pkgs.gmp
    skipCheck
  ];

  gnugrep = port [
    pkgs.gnugrep
    (src "3.11" (gnu "grep") "sha256-HbKu3eidDepCsW2VKPiUyNFdrk4ZC1muzHj1qVEnbqs=")
    (patch ./ports/patch/grep-3.11.patch)
    { inherit pcre2; }
    skipCheck
  ];

  gnumake = port [
    pkgs.gnumake
    (src "4.4.1" (gnuTarGz "make") "sha256-3Rb7HWe/q3mnL16DkHNcSePo5wtJRaFasfgd23hlj7M=")
    (patch ./ports/patch/make-4.4.1.patch)
    { guileSupport = false; }
  ];

  gnused = port [
    pkgs.gnused
    (src "4.9" (gnu "sed") "sha256-biJrcy4c1zlGStaGK9Ghq6QteYKSLaelNRljHSSXUYE=")
    (patch ./ports/patch/sed-4.9.patch)
    skipCheck
  ];

  gnutar = port [
    pkgs.gnutar
    (src "1.35" (gnu "tar") "sha256-TWL/NzQux67XSFNTI5MMfPlKz3HDWRiCsmp+pQ8+3BY=")
    (patch ./ports/patch/tar-1.35.patch)
    { aclSupport = false; }
  ];

  gnum4 = port [
    pkgs.gnum4
    (src "1.4.19" (gnu "m4") "sha256-Y67eXG0zttmxNRHNC+LKwEby5w/QoHqpVzoEqCeDr5Y=")
    (patch ./ports/patch/m4-1.4.19.patch)
  ];

  gtest = port [ pkgs.gtest ];

  inetutils = port [
    pkgs.inetutils
    { inherit ncurses; }
    { inherit libxcrypt; }
  ];

  strace = port [
    pkgs.strace
    { inherit libunwind; }
    { inherit elfutils; }
    (use { postPatch = ''sed -i 's/ vfork/ fork/g' */strace.c''; })
  ];

  libunwind = port [
    pkgs.libunwind
    { inherit xz; }
  ];

  elfutils = port [
    pkgs.elfutils
    { inherit zlib; }
    { inherit zstd; }
    { inherit bzip2; }
    { inherit xz; }
    { inherit sqlite; }
    { inherit curl; }
    { inherit json_c; }
    { inherit libmicrohttpd; }
    { inherit libarchive; }
    (tool depizloing-nm)
    (configure "--disable-symbol-versioning")
    (configure "--disable-debuginfod")
    #    (configure "--enable-libdebuginfod=dummy")
    (addCFlag "-Wno-error=unused-parameter")
    skipTests
  ];

  json_c = port [
    pkgs.json_c
  ];

  libmicrohttpd = port [
    (pkgs.callPackage ./libmicrohttpd.nix { })
    { inherit curl; }
  ];

  jq = port [
    pkgs.jq
    { inherit oniguruma; }
  ];

  keyutils = port [
    pkgs.keyutils
    (src "1.6.3" (
      v:
      "https://git.kernel.org/pub/scm/linux/kernel/git/dhowells/keyutils.git/snapshot/keyutils-${v}.tar.gz"
    ) "sha256-ph1XBhNq5MBb1I+G2GvP29iN2L1RB+Phlckkz8Gzm7Q=")
    (patch ./ports/patch/keyutils-1.6.3.patch)
    (skipPatch "after_eq")
  ];

  lesspipe = port [
    pkgs.lesspipe
    { inherit perl; }
    { inherit bash; }
  ];

  libarchive = port [
    pkgs.libarchive
    (src "3.7.4" (github "libarchive/libarchive" (
      v: "v${v}/libarchive-${v}.tar.xz"
    )) "sha256-+Id1XENKc2pgnL0o2H3b++nWo7tbcDwiwC9q+AqAJzU=")
    (patch ./ports/patch/libarchive-3.7.4.patch)
    { inherit zlib; }
    { inherit openssl; }
    { inherit libxml2; }
    { inherit bzip2; }
    { inherit zstd; }
    { inherit xz; }
    { inherit attr; }
    { inherit acl; }

    skipCheck
    (skipPatch "mac")
  ];

  libedit = port [
    pkgs.libedit
    (src "20240808-3.1" (
      v: "https://thrysoee.dk/editline/libedit-${v}.tar.gz"
    ) "sha256-XwVzNJ13xKSJZxkc3WY03Xql9jmMalf+A3zAJpbWCZ8=")
    (patch ./ports/patch/libedit-20240808-3.1.patch)
    { inherit ncurses; }
  ];

  libev = port [ pkgs.libev ];

  libffi = port [
    pkgs.libffi
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
    (pkgs.callPackage "${pkgs.path}/pkgs/development/libraries/libidn2" { })
    { inherit libunistring; }
  ];

  libkrb5 = port [
    pkgs.libkrb5
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
    pkgs.libpng
    (src "1.6.43" (
      v: "mirror://sourceforge/libpng/libpng-${v}.tar.xz"
    ) "sha256-Uw5O1JHsI91X2FYBy3XTVbUzDN9Vae7JkNn2Yw7W9tI=")
    (patch ./ports/patch/libpng-1.6.43.patch)
    { inherit zlib; }
  ];

  libpsl = port [
    pkgs.libpsl
    { inherit libidn2; }
    { inherit libunistring; }
  ];

  libssh2 = port [
    pkgs.libssh2
    { inherit zlib; }
    { inherit openssl; }
    (tool depizloing-nm)
    (tool pkgs.pkg-config)
    skipCheck
    (configure "--disable-examples-build")
  ];

  libtool = port [
    pkgs.libtool
    { inherit m4; }
    { inherit file; }
  ];

  libunistring = port [ pkgs.libunistring ];

  libuuid = util-linux;

  libuv = port [
    pkgs.libuv
    (src "1.48.0" (
      v: "https://dist.libuv.org/dist/v${v}/libuv-v${v}.tar.gz"
    ) "sha256-fx24rDaNidG68WO6wepf5RIGl6c5EMiuay//s1UdWfs=")
    (patch ./ports/patch/libuv-v1.48.0.patch)
  ];

  libxcrypt = port [
    pkgs.libxcrypt
    (src "4.4.36" (github "besser82/libxcrypt" (
      v: "v${v}/libxcrypt-${v}.tar.xz"
    )) "sha256-5eH0yu4KAd4q7ibjE4gH1tPKK45nKHlm0f79ZeH9iUM=")
    (patch ./ports/patch/libxcrypt-4.4.36.patch)
    (tool depizloing-nm)
    skipCheck
  ];

  libxml2 = port [
    pkgs.libxml2
    (patch ./ports/patch/libxml2-2.14.4.patch)
    { inherit zlib; }
    { inherit ncurses; }
    { pythonSupport = false; }
    skipCheck
  ];

  lighttpd = port [
    pkgs.lighttpd
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

  lua = pkgs.callPackage ./ports/lua.nix {
    inherit
      filenv
      filcc
      ncurses
      readline
      pkgs
      ;
  };

  m4 = gnum4;

  nano = port [
    pkgs.nano
    { inherit ncurses; }
  ];

  nethack = port [
    pkgs.nethack
    { inherit ncurses; }
  ];

  # ngtcp2 = port [
  #   pkgs.ngtcp2
  #   { inherit brotli; }
  #   { inherit libev; }
  #   { inherit nghttp3; }
  #   { inherit openssl; }
  # ];

  nghttp2 = port [
    pkgs.nghttp2
    { inherit zlib; }
    { inherit openssl; }
    (tool depizloing-nm)
    (configure "--disable-app")
    (addCFlag "-Wno-deprecated-literal-operator")
  ];

  nghttp3 = port [ pkgs.nghttp3 ];

  oniguruma = port [ pkgs.oniguruma ];

  openssh = port [
    pkgs.openssh
    (src "9.8p1" (
      v: "mirror://openbsd/OpenSSH/portable/openssh-${v}.tar.gz"
    ) "sha256-3YvQAqN5tdSZ37BQ3R+pr4Ap6ARh9LtsUjxJlz9aOfM=")
    (patch ./ports/patch/openssh-9.8p1.patch)
    {
      inherit
        zlib
        libedit
        openssl
        #        libfido2
        ldns
        pam
        ;
    }
    skipCheck
    { withFIDO = false; }
  ];

  libfido2 = port [
    pkgs.libfido2
    { inherit zlib openssl libcbor; }
    (use {
      buildInputs = [
        zlib
        openssl
        libcbor
        # systemd is too big and complicated to port right now
      ];
    })
    (addCMakeFlag "-DUSE_PCSC=OFF")
  ];

  libcbor = port [
    pkgs.libcbor
    { inherit cmocka; }
    { inherit libfido2; }
    (addCMakeFlag "-DCMAKE_VERBOSE_MAKEFILE=ON")
    (addCMakeFlag "-DCMAKE_NO_EXAMPLES=ON")
    (addCMakeFlag "-DCMAKE_SANITIZE=OFF")
    skipTests
  ];

  cmocka = port [
    pkgs.cmocka
    skipTests
    (addCMakeFlag "-DWITH_EXAMPLES=OFF")
  ];

  ldns = port [
    pkgs.ldns
    { inherit openssl; }
    (tool depizloing-nm)
  ];

  pam = port [
    pkgs.linux-pam
    { inherit libxcrypt db4; }
    (tool depizloing-nm)
    skipCheck
  ];

  pcre2 = port [
    pkgs.pcre2
    (src "10.44" (github "PCRE2Project/pcre2" (
      v: "pcre2-${v}/pcre2-${v}.tar.bz2"
    )) "sha256-008C4RPPcZOh6/J3DTrFJwiNSF1OBH7RDl0hfG713pY=")
  ];

  perl = port [
    pkgs.perl
    (src "5.40.0" (
      v: "https://www.cpan.org/src/5.0/perl-${v}.tar.gz"
    ) "sha256-x0A0jzVzljJ6l5XT6DI7r9D+ilx4NfwcuroMyN/nFh8=")
    (patch ./ports/patch/perl-5.40.0.patch)
    { inherit zlib; }
    skipCheck
    tranquilize
  ];

  procps = port [
    pkgs.procps
    { inherit ncurses; }
    { withSystemd = false; }
    (patch ./ports/patch/procps-ng-4.0.4.patch)
  ];

  pkgconf-unwrapped = port [
    pkgs.pkgconf-unwrapped
    (tool depizloing-nm)
    parallelize
  ];

  pkgconf = pkgs.callPackage (pkgs.path + "/pkgs/build-support/pkg-config-wrapper") {
    pkg-config = pkgconf-unwrapped;
    baseBinName = "pkgconf";
  };

  python3 = port [
    pkgs.python3
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
    skipCheck
    (tool pkgs.python3)
    (tool pkgs.autoreconfHook)
    (tool pkgs.autoconf)
    (tool pkgs.automake)
    (tool pkgs.libtool)
    (tool pkgs.autoconf-archive)
    (tool pkgs.m4)
    (tool pkgs.pkg-config)
    (removeCFlag "-Wa,--compress-debug-sections")
  ];

  quickjs = port [
    pkgs.quickjs
    (src "2024-02-14" (
      v: "https://bellard.org/quickjs/quickjs-2024-01-13.tar.xz"
    ) "sha256-PEv4+JW/pUvrSGyNEhgRJ3Hs/FrDvhA2hR70FWghLgM=")
    (patch ./ports/patch/quickjs.patch)
    skipCheck
  ];

  readline = port [
    pkgs.readline
    { inherit ncurses; }
  ];

  runit = port [
    pkgs.runit
    (patch ./runit-pid-namespace.patch)
  ];

  sqlite = port [
    pkgs.sqlite
    { inherit readline; }
    { inherit ncurses; }
    { interactive = true; }
    skipCheck
    (removeCFlag "-DSQLITE_ENABLE_STMT_SCANSTATUS")
  ];

  tcl = port [ pkgs.tcl ];

  # C99 Prolog implementation
  trealla = port [
    pkgs.trealla
    { inherit openssl; }
    { inherit libffi; }
    { inherit readline; }
    { lineEditingLibrary = "readline"; }
    (src "2.84.14" (
      v: "https://github.com/trealla-prolog/trealla/archive/v${v}.tar.gz"
    ) "sha256-W1erZMHlX3s0Px62LHoMAcHWUeepDk3T63/R2QAyDAQ=")

    (patch ./patches/trealla-filc-ffi-zptrtable.patch)

    # many fail with thwart in `bif_iso_write` hitting `isatty`.
    # also slow
    skipTests
  ];

  tree-sitter = port [
    pkgs.tree-sitter
    { inherit (pkgs) installShellFiles; }
  ];

  unibilium = port [
    pkgs.unibilium
    { inherit ncurses; }
  ];

  util-linux = port [
    pkgs.util-linux
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

  which = port [ pkgs.which ];

  xz = port [
    pkgs.xz
    (src "5.6.2" (github "tukaani-project/xz" (
      v: "v${v}/xz-${v}.tar.xz"
    )) "sha256-qds7s9ZOJIoPrpY/j7a6hRomuhgi5QTcDv0YqAxibK8=")
    (patch ./ports/patch/xz-5.6.2.patch)
    (tool pkgs.automake116x)
    (tool pkgs.autoconf)
    skipCheck
  ];

  zlib-ng = port [
    pkgs.zlib-ng
    (src "2.2.4" (github "zlib-ng/zlib-ng" (
      v: "${v}.tar.gz"
    )) "sha256-pzNDwwk+XNxQ2Td5l8OBW4eP0RC/ZRHCx3WfKvuQ9aM=")
    { inherit gtest; }
  ];

  zstd = port [
    pkgs.zstd
    (patch ./ports/patch/zstd-1.5.6.patch)
    { inherit bashNonInteractive; }
    skipCheck
    (addCFlag "-DZSTD_DISABLE_ASM")
  ];

  wasm3 = port [
    (pkgs.callPackage ./wasm3.nix { })
  ];

  kittydoom = port [
    (pkgs.callPackage ./kitty-doom.nix { })
  ];
}
