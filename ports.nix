# Fil-C package ports as overlay transformers
# Each port returns an attribute transformer: old -> { patches = ...; ... }
# Dependencies are handled automatically by Nix cross-compilation.

{
  pkgs,
}:
let
  DSL = import ./portconf.nix {
    inherit lib pkgs;
  };
  inherit (DSL)
    buildPort
    arg
    use
    src
    broken
    skipTests
    skipCheck
    parallelize
    serialize
    tool
    link
    patch
    skipPatch
    removeCFlag
    addCFlag
    removeCMakeFlag
    addCMakeFlag
    configure
    removeConfigureFlag
    wip
    depizloing-nm
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
  ];

  openssl = port [
    ./ports/openssl.nix
  ];

  libevent = port [
    pkgs.libevent
    (src "2.1.12" (github "libevent/libevent" (
      v: "release-${v}-stable/libevent-${v}-stable.tar.gz"
    )) "sha256-kubeG+nsF2Qo/SNnZ35hzv/C7hyxGQNQN6J9NGsEA7s=")
    (patch ./ports/patch/libevent-2.1.12.patch)
  ];

  ncurses = port [ pkgs.ncurses ];

  utf8proc = port [ pkgs.utf8proc ];

  libutempter = port [
    pkgs.libutempter
    (arg { glib = null; })
  ];

  tmux = port [
    pkgs.tmux
    (arg { withSystemd = false; })
  ];

  libsepol = port [
    pkgs.libsepol
    (src "3.9" (github "SELinuxProject/selinux" (
      v: "releases/download/v${v}/libsepol-${v}.tar.gz"
    )) "sha256-umMLWeUMX7+endRes3NPNzz3jWidjBDFNxFMm9dp+i4=")
    (patch ./ports/patch/libsepol-3.9.patch)
  ];

  # Work in progress (alphabetically sorted)
  acl = port [ pkgs.acl ];

  attr = port [
    pkgs.attr
    (src "2.5.2" (
      v: "mirror://savannah/attr/attr-${v}.tar.gz"
    ) "sha256-Ob9nRS+kHQlIwhl2AQU/SLPXigKTiXNDMqYwmmgMbIc=")
    (patch ./ports/patch/attr-2.5.2.patch)
  ];

  autoconf = port [ pkgs.autoconf ];

  automake = port [ pkgs.automake ];

  bash = port [
    pkgs.bash
    (arg { interactive = true; })
    skipCheck
  ];

  bashNonInteractive = port [
    pkgs.bash
    (arg { interactive = false; })
    skipCheck
  ];

  bc = port [ pkgs.bc ];

  bison = port [
    pkgs.bison
    (src "3.8.2" (gnu "bison") "sha256-m7oCFMz38QecXVkhAEUie89hlRmEDr+oDNOEnP9aW/I=")
    (patch ./ports/patch/bison-3.8.2.patch)
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
    skipCheck
  ];

  curl = port [
    pkgs.curlMinimal
    (arg { idnSupport = true; })
    (arg { pslSupport = true; })
    (arg { zstdSupport = true; })
    (arg { brotliSupport = true; })
    (arg { scpSupport = false; })
    skipCheck
  ];

  dash = port [
    pkgs.dash
    (src "0.5.12" (
      v: "http://gondor.apana.org.au/~herbert/dash/files/dash-${v}.tar.gz"
    ) "sha256-akdKxG6LCzKRbExg32lMggWNMpfYs4W3RQgDDKSo8oo=")
    (patch ./ports/patch/dash-0.5.12.patch)
  ];

  db4 = db48;

  db48 = port [ pkgs.db48 ];

  diffutils = port [
    pkgs.diffutils
    (src "3.10" (gnu "diffutils") "sha256-kOXpPMck5OvhLt6A3xY0Bjx6hVaSaFkZv+YLVWyb0J4=")
    (patch ./ports/patch/diffutils-3.10.patch)
    (use { postPatch = "patchShebangs man/help2man"; })
    skipCheck
  ];

  ed = port [
    pkgs.ed
    (arg { runtimeShellPackage = bash; })
  ];

  emacs = port [
    pkgs.emacs
    (arg {
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
    })
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
    skipCheck
  ];

  findutils = port [ pkgs.findutils ];

  flex = port [ pkgs.flex ];

  git = port [
    pkgs.git
    (src "2.46.0" (
      v: "https://www.kernel.org/pub/software/scm/git/git-${v}.tar.xz"
    ) "sha256-fxI0YqKLfKPr4mB0hfcWhVTCsQ38FVx+xGMAZmrCf5U=")
    (skipPatch "git-send-email-honor-PATH.patch")
    (patch ./ports/patch/git-2.46.0.patch)
    (arg { withManual = false; })
    (arg { perlSupport = false; })
    (arg { pythonSupport = false; })
    (arg { sendEmailSupport = false; })
    { zlib-ng = zlib; } # dependency override - will be ignored in overlay mode
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
    skipCheck
  ];

  gnumake = port [
    pkgs.gnumake
    (src "4.4.1" (gnuTarGz "make") "sha256-3Rb7HWe/q3mnL16DkHNcSePo5wtJRaFasfgd23hlj7M=")
    (patch ./ports/patch/make-4.4.1.patch)
    (arg { guileSupport = false; })
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
    (arg { aclSupport = false; })
  ];

  gnum4 = port [
    pkgs.gnum4
    (src "1.4.19" (gnu "m4") "sha256-Y67eXG0zttmxNRHNC+LKwEby5w/QoHqpVzoEqCeDr5Y=")
    (patch ./ports/patch/m4-1.4.19.patch)
  ];

  gtest = port [ pkgs.gtest ];

  inetutils = port [ pkgs.inetutils ];

  strace = port [
    pkgs.strace
    (use { postPatch = ''sed -i 's/ vfork/ fork/g' */strace.c''; })
  ];

  libunwind = port [ pkgs.libunwind ];

  elfutils = port [
    pkgs.elfutils
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
  ];

  jq = port [ pkgs.jq ];

  keyutils = port [
    pkgs.keyutils
    (src "1.6.3" (
      v:
      "https://git.kernel.org/pub/scm/linux/kernel/git/dhowells/keyutils.git/snapshot/keyutils-${v}.tar.gz"
    ) "sha256-ph1XBhNq5MBb1I+GGGvP29iN2L1RB+Phlckkz8Gzm7Q=")
    (patch ./ports/patch/keyutils-1.6.3.patch)
    (skipPatch "after_eq")
  ];

  lesspipe = port [ pkgs.lesspipe ];

  libarchive = port [
    pkgs.libarchive
    (src "3.7.4" (github "libarchive/libarchive" (
      v: "v${v}/libarchive-${v}.tar.xz"
    )) "sha256-+Id1XENKc2pgnL0o2H3b++nWo7tbcDwiwC9q+AqAJzU=")
    (patch ./ports/patch/libarchive-3.7.4.patch)
    skipCheck
    (skipPatch "mac")
  ];

  libedit = port [
    pkgs.libedit
    (src "20240808-3.1" (
      v: "https://thrysoee.dk/editline/libedit-${v}.tar.gz"
    ) "sha256-XwVzNJ13xKSJZxkc3WY03Xql9jmMalf+A3zAJpbWCZ8=")
    (patch ./ports/patch/libedit-20240808-3.1.patch)
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

  # libiconv comes from glibc in cross-compilation
  libiconv = {
    attrs = old: { };
    overrideArgs = { };
  };

  libidn2 = port [
    (pkgs.callPackage "${pkgs.path}/pkgs/development/libraries/libidn2" { })
  ];

  libkrb5 = port [
    pkgs.libkrb5
    (src "1.21.3" (
      v: "https://kerberos.org/dist/krb5/1.21/krb5-${v}.tar.gz"
    ) "sha256-t6TNXq1n+wi5gLIavRUP9yF+heoyDJ7QxtrdMEhArTU=")
    (patch ./ports/patch/krb5-1.21.3.patch)
    (use { patchFlags = [ "-p2" ]; })
  ];

  libpng = port [
    pkgs.libpng
    (src "1.6.43" (
      v: "mirror://sourceforge/libpng/libpng-${v}.tar.xz"
    ) "sha256-alygZSOSotfJ2yrltAIQhDwLvAgcvUEIJasAzFnxSmw=")
    (patch ./ports/patch/libpng-1.6.43.patch)
  ];

  libpsl = port [ pkgs.libpsl ];

  libssh2 = port [
    pkgs.libssh2
    skipCheck
    (configure "--disable-examples-build")
  ];

  libtool = port [ pkgs.libtool ];

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
    skipCheck
  ];

  libxml2 = port [
    pkgs.libxml2
    (patch ./ports/patch/libxml2-2.14.4.patch)
    (arg { pythonSupport = false; })
    skipCheck
  ];

  lighttpd = port [
    pkgs.lighttpd
    (patch ./lighttpd-filc.patch)
    { lua5_1 = lua; } # dependency override - will be ignored in overlay mode
    { linux-pam = pam; } # dependency override - will be ignored in overlay mode
    (arg { enableMagnet = true; })
    (arg { enableWebDAV = true; })
    (arg { enablePam = true; })
    skipCheck
    (configure "--with-zlib")
    (configure "--with-bzip2")
    (configure "--with-brotli")
    (configure "--with-zstd")
    (configure "--with-krb5")
  ];

  # lua is a custom derivation that doesn't fit the overlay model
  # TODO: Convert to use nixpkgs lua with patches, or handle specially
  # lua = pkgs.callPackage ./ports/lua.nix {
  #   inherit
  #     filenv
  #     filcc
  #     ncurses
  #     readline
  #     pkgs
  #     ;
  # };
  lua = {
    attrs = old: { };
    overrideArgs = { };
  };

  m4 = gnum4;

  nano = port [ pkgs.nano ];

  nethack = port [ pkgs.nethack ];

  # ngtcp2 = port [
  #   pkgs.ngtcp2
  #   { inherit brotli; }
  #   { inherit libev; }
  #   { inherit nghttp3; }
  #   { inherit openssl; }
  # ];

  nghttp2 = port [
    pkgs.nghttp2
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
    skipCheck
    (arg { withFIDO = false; })
  ];

  # libfido2 = port [
  #   pkgs.libfido2
  #   { inherit zlib openssl libcbor; }
  #   (use {
  #     buildInputs = [
  #       zlib
  #       openssl
  #       libcbor
  #       # systemd is too big and complicated to port right now
  #     ];
  #   })
  #   (addCMakeFlag "-DUSE_PCSC=OFF")
  # ];

  libcbor = port [
    pkgs.libcbor
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

  ldns = port [ pkgs.ldns ];

  pam = port [
    pkgs.linux-pam
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
    skipCheck
  ];

  procps = port [
    pkgs.procps
    (arg { withSystemd = false; })
    (patch ./ports/patch/procps-ng-4.0.4.patch)
  ];

  python3 = port [
    pkgs.python3
    (src "3.12.5" (
      v: "https://www.python.org/ftp/python/${v}/Python-${v}.tar.xz"
    ) "sha256-+oouEsXmILCfU+ZbzYdVDS5aHi4Ev4upkdzFUROHY5c=")
    (patch ./ports/patch/Python-3.12.5.patch)
    (arg { mimetypesSupport = true; })
    skipCheck
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

  readline = port [ pkgs.readline ];

  runit = port [
    pkgs.runit
    (patch ./runit-pid-namespace.patch)
  ];

  scrypt = port [
    pkgs.scrypt
    (tool depizloing-nm)
    skipTests
  ];

  sqlite = port [
    pkgs.sqlite
    (arg { interactive = true; })
    skipCheck
    (removeCFlag "-DSQLITE_ENABLE_STMT_SCANSTATUS")
  ];

  tcl = port [ pkgs.tcl ];

  tinycc = port [
    pkgs.tinycc
    (patch ./tinycc-alignment.patch)
    (use (old: {
      preConfigure = ''
        echo ${old.version} > VERSION
      '';

      # TCC is special: we build it WITH Fil-C (host=gnufilc0) but it compiles
      # FOR native x86_64-linux (target=gnu). So it needs native glibc paths,
      # not the Fil-C sysroot paths that stdenv.cc.libc would give us.
      configureFlags = [
        "--cc=$CC"
        "--ar=$AR"
        "--crtprefix=${pkgs.glibc}/lib"
        "--sysincludepaths={B}/include:${pkgs.glibc.dev}/include"
        "--libpaths=$lib/lib/tcc:$lib/lib:${pkgs.glibc}/lib"
        "--elfinterp=${pkgs.glibc}/lib/ld-linux-x86-64.so.2"
      ];

    }))
    (tool pkgs.glibc.bin) # for ldd

    # TCC's -run (JIT) feature is incompatible with Fil-C because:
    # 1. Requires W+X memory (writable + executable)
    # 2. Generated code isn't instrumented by Fil-C
    # 3. Can't reconstruct capabilities from integer addresses in tcc_relocate_ex
    # Almost all TCC tests use -run.
    skipTests
  ];

  tor = port [
    pkgs.tor
    (arg {
      systemd = null;
      libseccomp = null;
      libcap = null;
    })

    (configure "ac_cv_header_execinfo_h=no")
    (configure "ac_cv_func_backtrace=no")
    (configure "ac_cv_func_backtrace_symbols=no")
    (configure "ac_cv_func_backtrace_symbols_fd=no")
    (configure "ac_cv_search_backtrace=no")
    (addCFlag "-DED25519_NO_INLINE_ASM=1")

    skipTests # pass 17, skip 2, fail 6
  ];

  torsocks = port [
    pkgs.torsocks
    (tool pkgs.glibc.bin)
    (tool depizloing-nm)
    (arg { libcap = null; })
    (use {
      postPatch = ''
        # Patch torify_app()
        sed -i \
          -e 's,\(local app_path\)=`which $1`,\1=`type -P $1`,' \
          src/bin/torsocks.in
      '';
    })
    skipTests # 2 failing tests, didn't look into it yet
  ];

  # C99 Prolog implementation
  trealla = port [
    pkgs.trealla
    (arg { lineEditingLibrary = "readline"; })
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
    { inherit (pkgs) installShellFiles; } # build tool - will be ignored in overlay mode
  ];

  unibilium = port [ pkgs.unibilium ];

  util-linux = port [
    pkgs.util-linux
    (arg { capabilitiesSupport = false; })
    (arg { cryptsetupSupport = false; })
    (arg { nlsSupport = false; })
    (arg { ncursesSupport = false; })
    (arg { pamSupport = true; })
    (arg { shadowSupport = true; })
    (arg { systemdSupport = false; })
    (arg { translateManpages = false; })
    parallelize
  ];

  which = port [ pkgs.which ];

  xz = port [
    pkgs.xz
    (src "5.6.2" (github "tukaani-project/xz" (
      v: "v${v}/xz-${v}.tar.xz"
    )) "sha256-qds7s9ZOJIoPrpY/j7a6hRomuhgi5QTcDv0YqAxibK8=")
    (patch ./ports/patch/xz-5.6.2.patch)
    skipCheck
    (tool pkgs.automake116x)
    (tool pkgs.autoconf)
  ];

  zlib-ng = port [
    pkgs.zlib-ng
    (src "2.2.4" (github "zlib-ng/zlib-ng" (
      v: "${v}.tar.gz"
    )) "sha256-pzNDwwk+XNxQ2Td5l8OBW4eP0RC/ZRHCx3WfKvuQ9aM=")
  ];

  zstd = port [
    pkgs.zstd
    (patch ./ports/patch/zstd-1.5.6.patch)
    skipCheck
    (addCFlag "-DZSTD_DISABLE_ASM")
  ];

  wasm3 = port [
    (pkgs.callPackage ./wasm3.nix { })
  ];

  kittydoom = port [
    (pkgs.callPackage ./kitty-doom.nix { })
  ];

  # Mark packages as broken on gnufilc0 to prevent accidental dependencies
  systemd = broken "not yet ported";
  dbus = broken "not yet ported";
  gnutls = broken "too many dependencies";

  # GUI/display stuff we don't need
  gtk3 = broken "GUI not supported";
  gtk4 = broken "GUI not supported";
  wayland = broken "GUI not supported";
  libX11 = broken "X11 not supported";
}
