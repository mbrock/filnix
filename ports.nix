# Fil-C package ports as overlay transformers
# Each port returns an attribute transformer: old -> { patches = ...; ... }
# Dependencies are handled automatically by Nix cross-compilation.

{
  pkgs,
  prev,
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

  libutempter = port [
    pkgs.libutempter
    (arg { glib = null; })
  ];

  nettle = port [
    pkgs.nettle
    (removeConfigureFlag "--enable-fat")
    (configure "--disable-assembler")
  ];

  gobject-introspection = port [
    pkgs.gobject-introspection
    (use (old: {
      # turn this thing off so glib builds perfectly
      meta = old.meta // {
        badPlatforms = [ "x86_64-linux" ];
        broken = true;
      };
    }))
  ];

  gobject-introspection-unwrapped = port [
    pkgs.gobject-introspection-unwrapped
    # (src "1.81.4" (
    #   v:
    #   "mirror://gnome/sources/gobject-introspection/${lib.versions.majorMinor v}/gobject-introspection-${v}.tar.xz"
    # ) "sha256-CruZA9tDMLK157qEOde7xIu0Ah8lD41Pu36oFtQAZDA=")
    (use (old: {
      # lol futile attempt absolutely doesn't work
      postPatch = (old.postPatch or "") + ''
        sed -i 's/2.82.0/2.80.4/' meson.build
        sed -i 's/case G_TYPE/case (uintptr_t) G_TYPE/g' $(find . -name '*.c')
      '';
      env = (old.env or { }) // {
        NIX_CFLAGS_COMPILE = toString [
          "-Wno-error=nonnull"
          "-DG_DISABLE_CAST_CHECKS"
        ];
      };
    }))
  ];

  glib = port [
    # wtf
    pkgs.glib
    (src "2.80.4" (
      v: "mirror://gnome/sources/glib/${lib.versions.majorMinor v}/glib-${v}.tar.xz"
    ) "sha256-JOApxd/JtE5Fc2l63zMHipgnxIk4VVAEs7kJb6TqA08=")
    (patch ./ports/patch/glib-2.80.4.patch)
    (patch ./glib-inline.patch)
    (skipPatch "split-dev-programs.patch")
    (patch ./glib-split-backport.patch)
    (arg { libsysprof-capture = null; })
    skipTests
    (use {
      mesonFlags = [
        "-Ddevbindir=${placeholder "dev"}/bin"
        "-Dglib_debug=disabled"
        "-Ddocumentation=true"
        (lib.mesonBool "dtrace" false)
        (lib.mesonBool "systemtap" false)
        "-Dnls=enabled"
        (lib.mesonEnable "introspection" false)
        "-Dtests=false"
      ];
    })
  ];

  tmux = port [
    pkgs.tmux
    (arg { withSystemd = false; })
  ];

  libsepol = port [
    pkgs.libsepol
    # (src "3.9" (github "SELinuxProject/selinux" (
    #   v: "releases/download/v${v}/libsepol-${v}.tar.gz"
    # )) "sha256-umMLWeUMX7+endRes3NPNzz3jWidjBDFNxFMm9dp+i4=")
    (patch ./ports/patch/libsepol-3.9.patch)
  ];

  libselinux = port [
    pkgs.libselinux
    (patch ./ports/patch/libselinux-3.9.patch)
  ];

  libgpg-error =
    let
      lock-obj-gnufilc0 = pkgs.writeText "lock-obj-pub.x86_64-unknown-linux-gnufilc0.h" ''
        ## File created by gen-posix-lock-obj - DO NOT EDIT
        ## To be included by mkheader into gpg-error.h

        typedef struct
        {
          long _vers;
          union {
            volatile char _priv[40];
            long _x_align;
            long *_xp_align;
          } u;
        } gpgrt_lock_t;

        #define GPGRT_LOCK_INITIALIZER {1,{{0,0,0,0,0,0,0,0, \
                                            0,0,0,0,0,0,0,0, \
                                            0,0,0,0,0,0,0,0, \
                                            0,0,0,0,0,0,0,0, \
                                            0,0,0,0,0,0,0,0}}}
        ##
        ## Local Variables:
        ## mode: c
        ## buffer-read-only: t
        ## End:
        ##
      '';
    in
    port [
      pkgs.libgpg-error
      (use {
        postPatch = ''
          cp ${lock-obj-gnufilc0} src/syscfg/lock-obj-pub.x86_64-unknown-linux-gnufilc0.h
        '';
        postConfigure = ''
          cp ${lock-obj-gnufilc0} src/lock-obj-pub.native.h
        '';
      })
    ];

  libgcrypt = port [
    pkgs.libgcrypt
    (configure "--disable-asm")
    (configure "gcry_cv_gcc_amd64_platform_as_ok=no")
    (use { configurePlatforms = [ "host" ]; })
    (use {
      buildPhase = ''
        sed -i '/HAVE_GCC_ASM_VOLATILE_MEMORY/d' config.h
        touch config.status
        make -j$NIX_BUILD_CORES
      '';
    })
  ];

  libtasn1 = port [
    pkgs.libtasn1
    skipTests
  ];

  attr = port [
    pkgs.attr
    (src "2.5.2" (
      v: "mirror://savannah/attr/attr-${v}.tar.gz"
    ) "sha256-Ob9nRS+kHQlIwhl2AQU/SLPXigKTiXNDMqYwmmgMbIc=")
    (patch ./ports/patch/attr-2.5.2.patch)
  ];

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

  bison = port [
    pkgs.bison
    (src "3.8.2" (gnu "bison") "sha256-m7oCFMz38QecXVkhAEUie89hlRmEDr+oDNOEnP9aW/I=")
    (patch ./ports/patch/bison-3.8.2.patch)
    skipTests
  ];

  busybox = port [
    pkgs.busybox
    (use {
      enableStatic = false;
      enableAppletSymlinks = false;
      enableMinimal = false;
    })
  ];

  cmake = port [
    pkgs.cmake
    (src "3.30.2" (
      v: "https://cmake.org/files/v3.30/cmake-${v}.tar.gz"
    ) "sha256-RgdMeB7M68Qz6Y8Lv6Jlyj/UOB8kXKOxQOdxFTHWDbI=")
    skipCheck
    (addCMakeFlag "-DCMAKE_VERBOSE_MAKEFILE=ON")

    # nixpkgs also attempts to override these,
    # but it relies on a target prefix and not a full path.
    # We don't seem to set up the target prefix correctly,
    # so we just use the full path.
    (addCMakeFlag "-DCMAKE_CXX_COMPILER=${pkgs.lib.getBin prev.stdenv.cc}/bin/c++")
    (addCMakeFlag "-DCMAKE_C_COMPILER=${pkgs.lib.getBin prev.stdenv.cc}/bin/cc")

    # add -lm to the link flags for `lround` etc
    (addCMakeFlag "-DCMAKE_EXE_LINKER_FLAGS=-lm")
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

  gdbm = port [
    pkgs.gdbm
    (tool depizloing-nm)
  ];

  dash = port [
    pkgs.dash
    (src "0.5.12" (
      v: "http://gondor.apana.org.au/~herbert/dash/files/dash-${v}.tar.gz"
    ) "sha256-akdKxG6LCzKRbExg32lMggWNMpfYs4W3RQgDDKSo8oo=")
    (patch ./ports/patch/dash-0.5.12.patch)
  ];

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

  e2fsprogs = port [
    pkgs.e2fsprogs
    (arg { withFuse = false; })
    skipTests
  ];

  gettext = port [
    pkgs.gettext
    (tool depizloing-nm)
    (use (old: {
      env = old.env // {
        gettextNeedsLdflags = false;
      };
    }))
  ];

  luajit = port [
    pkgs.luajit
    (use (old: {
      meta = old.meta // {
        badPlatforms = [ "x86_64-linux" ];
        broken = true;
      };
    }))
  ];

  rspamd = port [
    pkgs.rspamd
    (arg { withLuaJIT = false; })
  ];

  emacs30 = port [
    pkgs.emacs30
    (arg {
      # Disable TLS for now (gnutls has too many deps)
      gnutls = null;
      systemd = null;
      mailutils = null;
      dbus = null;
      harfbuzz = null;
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
    (tool depizloing-nm)
    (src "2.7.1" (github "libexpat/libexpat" (
      v: "R_${builtins.replaceStrings [ "." ] [ "_" ] v}/expat-${v}.tar.xz"
    )) "sha256-NUVSVEuPmQEuUGL31XDsd/FLQSo/9cfY0NrmLA0hfDA=")
    (patch ./ports/patch/expat-2.7.1.patch)
  ];

  file = port [
    pkgs.file
    skipCheck
  ];

  fontconfig = port [
    pkgs.fontconfig
    skipCheck # these failures look pretty sus tbqh
  ];

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

  libbsd = port [
    pkgs.libbsd
    (tool depizloing-nm)
    serialize
    (use (old: {
      meta = old.meta // {
        badPlatforms = [ "x86_64-linux" ];
        broken = true;
      };
    }))
  ];

  rhash = port [
    pkgs.rhash
    (use {
      # -Wl,--version-script,exports.sym,-soname,librhash.so.1
      preConfigure = ''
        sed -i 's/,-soname/ -Wl,-soname/' configure
      '';
    })
    (addCFlag "-DRHASH_NO_ASM=1")
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

  strace = port [
    pkgs.strace
    (use { postPatch = ''sed -i 's/ vfork/ fork/g' */strace.c''; })
  ];

  elfutils = port [
    pkgs.elfutils
    (configure "--disable-symbol-versioning")
    (configure "--disable-debuginfod")
    #    (configure "--enable-libdebuginfod=dummy")
    (addCFlag "-Wno-error=unused-parameter")
    (arg { enableDebuginfod = false; })
    skipTests
  ];

  libmicrohttpd = port [
    (pkgs.callPackage ./libmicrohttpd.nix { })
  ];

  keyutils = port [
    pkgs.keyutils
    (src "1.6.3" (
      v:
      "https://git.kernel.org/pub/scm/linux/kernel/git/dhowells/keyutils.git/snapshot/keyutils-${v}.tar.gz"
    ) "sha256-ph1XBhNq5MBb1I+GGGvP29iN2L1RB+Phlckkz8Gzm7Q=")
    (patch ./ports/patch/keyutils-1.6.3.patch)
    (skipPatch "after_eq")
  ];

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

  libffi = port [
    pkgs.libffi
    (tool depizloing-nm)
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
    (use { postPatch = ""; })
    skipCheck
  ];

  libssh2 = port [
    pkgs.libssh2
    (tool depizloing-nm)
    skipCheck
    (configure "--disable-examples-build")
  ];

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
    #    { lua5_1 = lua; } # dependency override - will be ignored in overlay mode
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

  lzo = port [
    pkgs.lzo
    skipTests
    (tool depizloing-nm)
    (configure "--disable-asm")
  ];

  tree-sitter = broken "tries to cross compile rustc hahaha";

  nghttp2 = port [
    pkgs.nghttp2
    (configure "--disable-app")
    (addCFlag "-Wno-deprecated-literal-operator")
  ];

  openssh = port [
    pkgs.openssh
    (src "9.8p1" (
      v: "mirror://openbsd/OpenSSH/portable/openssh-${v}.tar.gz"
    ) "sha256-3YvQAqN5tdSZ37BQ3R+pr4Ap6ARh9LtsUjxJlz9aOfM=")
    (patch ./ports/patch/openssh-9.8p1.patch)
    skipCheck
    (arg { withFIDO = false; })
  ];

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

  python311 = broken "use python 3.12";
  python313 = broken "use python 3.12";

  python312 = port [
    pkgs.python312
    (src "3.12.5" (
      v: "https://www.python.org/ftp/python/${v}/Python-${v}.tar.xz"
    ) "sha256-+oouEsXmILCfU+ZbzYdVDS5aHi4Ev4upkdzFUROHY5c=")
    (patch ./ports/patch/Python-3.12.5.patch)
    (patch ./python-filc-triplet-detection.patch)
    (patch ./python-faulthandler.patch)
    (removeCFlag "-Wa,--compress-debug-sections")
    (arg { enableLTO = false; })
    (configure "--without-pymalloc")
    (configure "--without-freelists")
    (configure "ac_cv_func_chflags=no")
    (configure "ac_cv_func_lchflags=no")
    (configure "ac_cv_func_sigaltstack=no")
    (configure "ac_cv_gcc_asm_for_x64=no")
    (configure "ac_cv_gcc_asm_for_x87=no")

    # filcc panics on invalid super nintendo assembly
    # but configure only checks if it compiles :D
    (configure "ac_cv_gcc_asm_for_mc68881=no")

    (arg {
      packageOverrides = pyself: pyprev: {
        pytest-regressions =
          (pyprev.pytest-regressions.override {
            matplotlib = null;
            pandas = null;
            pillow = null;
          }).overrideAttrs
            (_: {
              doCheck = false;
              doInstallCheck = false;
            });

        annotated-types = pyprev.annotated-types.overrideAttrs (_: {
          doCheck = false;
          doInstallCheck = false;
        });

        tqdm = pyprev.tqdm.override { tkinter = null; };

        flask = pyprev.flask.overrideAttrs (_: {
          doCheck = false;
          doInstallCheck = false;
        });

        anyio = pyprev.anyio.overrideAttrs (_: {
          # these tests depend on `cryptography` which is Rust
          doCheck = false;
          doInstallCheck = false;
        });

        trio = pyprev.trio.overrideAttrs (_: {
          doCheck = false;
          doInstallCheck = false;
        });

        markdown = pyprev.markdown.overrideAttrs (_: {
          doCheck = false;
          doInstallCheck = false;
        });

        tagflow = pyself.buildPythonPackage {
          pname = "tagflow";
          version = "0.12.0-git";
          format = "pyproject";

          src = pkgs.fetchFromGitHub {
            owner = "lessrest";
            repo = "tagflow";
            rev = "eccedd29ccc58e2321f9332e05cf87a8130b6d4b";
            hash = "sha256-hkg4KbgVsZLSGi7sH4MDIP1M5n+ShHeXdM0HMUu35vo=";
          };

          nativeBuildInputs = with pyself; [
            hatchling
          ];

          propagatedBuildInputs = with pyself; [
            anyio
            trio
          ];

          doCheck = false;
          doInstallCheck = false;
        };
      };
    })
  ];

  pkgconf-unwrapped = port [
    pkgs.pkgconf-unwrapped
    (tool depizloing-nm)
  ];

  p11-kit = port [
    pkgs.p11-kit
    skipTests # 1 failure
  ];

  quickjs = port [
    pkgs.quickjs
    (src "2024-02-14" (
      v: "https://bellard.org/quickjs/quickjs-2024-01-13.tar.xz"
    ) "sha256-PEv4+JW/pUvrSGyNEhgRJ3Hs/FrDvhA2hR70FWghLgM=")
    (patch ./ports/patch/quickjs.patch)
    skipCheck
  ];

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

  util-linuxMinimal = port [
    pkgs.util-linuxMinimal
    # (arg { capabilitiesSupport = false; })
    # (arg { cryptsetupSupport = false; })
    # (arg { nlsSupport = false; })
    # (arg { ncursesSupport = false; })
    # (arg { pamSupport = true; })
    # (arg { shadowSupport = true; })
    # (arg { systemdSupport = false; })
    # (arg { translateManpages = false; })
    parallelize
  ];

  util-linux = util-linuxMinimal;

  shadow = port [
    pkgs.shadow
    (tool depizloing-nm)
  ];

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

  rustc = broken "oh sweet summer child";
}
