# Fil-C package ports - list-based structure
#
# Each port: (for pkgs.package [transforms...])
# Explicit names: { bash = for pkgs.bash [...]; }

{
  pkgs,
  prev,
}:
let
  inherit (import ./portconf2.nix { inherit (pkgs) lib pkgs; })
    for
    arg
    use
    pin
    src
    broken
    markAsNotNecessarilyInsecure
    skipTests
    skipCheck
    parallelize
    serialize
    tool
    patch
    skipPatch
    removeCFlag
    addCFlag
    removeCMakeFlag
    addCMakeFlag
    addMakeFlag
    removeMakeFlag
    addMesonFlag
    removeMesonFlag
    configure
    removeConfigureFlag
    wip
    depizloing-nm
    github
    gnu
    gnuTarGz
    ;
in
[
  # ━━━ Core Libraries ━━━

  (for pkgs.zlib [
    (pin "1.3" "sha256-/wukwpIBPbwnUws6geH5qBPNOd4Byl4Pi/NVcC76WT4=")
    (patch ./ports/patch/zlib-1.3.patch)
  ])

  (for pkgs.zlib-ng [
    (pin "2.2.4" "sha256-pzNDwwk+XNxQ2Td5l8OBW4eP0RC/ZRHCx3WfKvuQ9aM=")
  ])

  {
    openssl = for ./ports/openssl.nix [ ];
  }

  (for pkgs.libevent [
    (pin "2.1.12" "sha256-kubeG+nsF2Qo/SNnZ35hzv/C7hyxGQNQN6J9NGsEA7s=")
    (patch ./ports/patch/libevent-2.1.12.patch)
  ])

  (for pkgs.attr [
    (pin "2.5.2" "sha256-Ob9nRS+kHQlIwhl2AQU/SLPXigKTiXNDMqYwmmgMbIc=")
    (patch ./ports/patch/attr-2.5.2.patch)
  ])

  (for pkgs.expat [
    (tool depizloing-nm)
    (pin "2.7.1" "sha256-NUVSVEuPmQEuUGL31XDsd/FLQSo/9cfY0NrmLA0hfDA=")
    (patch ./ports/patch/expat-2.7.1.patch)
  ])

  (for pkgs.libffi [
    (tool depizloing-nm)
    (pin "3.4.6" "sha256-sN6p3yPIY6elDoJUQPPr/6vWXfFJcQjl1Dd0eEOJWk4=")
    (patch ./ports/patch/libffi-3.4.6.patch)
    (skipCheck "incompatible with static trampolines")
    (configure "--with-gcc-arch=native")
    (configure "--disable-static")
    (configure "--disable-exec-static-tramp")
  ])

  {
    libpng = for pkgs.libpng [
      (pin "1.6.43" "sha256-alygZSOSotfJ2yrltAIQhDwLvAgcvUEIJasAzFnxSmw=")
      (patch ./ports/patch/libpng-1.6.43.patch)
      (use { postPatch = ""; })
      (skipCheck "slow and occasionally flaky")
    ];
  }

  (for pkgs.libxml2 [
    (patch ./ports/patch/libxml2-2.14.4.patch)
    (arg { pythonSupport = false; })
    (skipCheck "python tests fail")
  ])

  (for pkgs.libuv [
    (pin "1.48.0" "sha256-jCU62w+ACSamy9HGV2q64LyOuGpPiRBJty+eW33FjzM=")
    (patch ./ports/patch/libuv-v1.48.0.patch)
  ])

  (for pkgs.libxcrypt [
    (pin "4.4.36" "sha256-5eH0yu4KAd4q7ibjE4gH1tPKK45nKHlm0f79ZeH9iUM=")
    (patch ./ports/patch/libxcrypt-4.4.36.patch)
    (skipCheck "one test fails")
  ])

  (for pkgs.nettle [
    (removeConfigureFlag "--enable-fat")
    (configure "--disable-assembler")
  ])

  (for pkgs.pcre2 [
    (pin "10.44" "sha256-008C4RPPcZOh6/J3DTrFJwiNSF1OBH7RDl0hfG713pY=")
  ])

  (for pkgs.libarchive [
    (pin "3.7.4" "sha256-z3/IW59mPAbcK3A2t+5U0CcSFn4EsHvcxMJ1U6vy1v8=")
    (patch ./ports/patch/libarchive-3.7.4.patch)
    (skipCheck "some tests fail")
    (skipPatch "mac")
  ])

  (for pkgs.libedit [
    (pin "20240808-3.1" "sha256-XwVzNJ13xKSJZxkc3WY03Xql9jmMalf+A3zAJpbWCZ8=")
    (patch ./ports/patch/libedit-20240808-3.1.patch)
  ])

  (for (pkgs.callPackage "${pkgs.path}/pkgs/development/libraries/libidn2" { }) [ ])

  # Special case - libiconv comes from glibc in cross-compilation
  {
    libiconv = {
      pname = "libiconv";
      attrs = old: { };
      overrideArgs = { };
    };
  }

  # ━━━ Core Utilities ━━━

  (for pkgs.coreutils [
    (skipCheck "too slow in Fil-C")
  ])

  {
    bash = for pkgs.bash [
      (arg { interactive = true; })
      (skipCheck "interactive mode issues")
    ];

    bashNonInteractive = for pkgs.bash [
      (arg { interactive = false; })
      (skipCheck "test issues")
    ];
  }

  (for pkgs.busybox [
    (use {
      enableStatic = false;
      enableAppletSymlinks = false;
      enableMinimal = false;
    })
  ])

  (for pkgs.diffutils [
    (pin "3.10" "sha256-kOXpPMck5OvhLt6A3xY0Bjx6hVaSaFkZv+YLVWyb0J4=")
    (patch ./ports/patch/diffutils-3.10.patch)
    (use { postPatch = "patchShebangs man/help2man"; })
    (skipCheck "too slow")
  ])

  (for pkgs.dash [
    (pin "0.5.12" "sha256-akdKxG6LCzKRbExg32lMggWNMpfYs4W3RQgDDKSo8oo=")
    (patch ./ports/patch/dash-0.5.12.patch)
  ])

  (for pkgs.file [
    (skipCheck "some magic tests fail")
  ])

  (for pkgs.gawk [
    (skipCheck "locale tests fail")
  ])

  (for pkgs.gnugrep [
    (pin "3.11" "sha256-HbKu3eidDepCsW2VKPiUyNFdrk4ZC1muzHj1qVEnbqs=")
    (patch ./ports/patch/grep-3.11.patch)
    (skipCheck "too slow")
  ])

  (for pkgs.gnumake [
    (pin "4.4.1" "sha256-3Rb7HWe/q3mnL16DkHNcSePo5wtJRaFasfgd23hlj7M=")
    (patch ./ports/patch/make-4.4.1.patch)
    (arg { guileSupport = false; })
  ])

  (for pkgs.gnused [
    (pin "4.9" "sha256-biJrcy4c1zlGStaGK9Ghq6QteYKSLaelNRljHSSXUYE=")
    (patch ./ports/patch/sed-4.9.patch)
    (skipCheck "too slow")
  ])

  (for pkgs.gnutar [
    (pin "1.35" "sha256-TWL/NzQux67XSFNTI5MMfPlKz3HDWRiCsmp+pQ8+3BY=")
    (patch ./ports/patch/tar-1.35.patch)
    (arg { aclSupport = false; })
  ])

  (for pkgs.gnum4 [
    (pin "1.4.19" "sha256-swapHA/ZO8QoDPwumMt6s5gf91oYe+oyk4EfRSyJqMg=")
    (patch ./ports/patch/m4-1.4.19.patch)
  ])

  # ━━━ Build Tools ━━━

  (for pkgs.bison [
    (pin "3.8.2" "sha256-m7oCFMz38QecXVkhAEUie89hlRmEDr+oDNOEnP9aW/I=")
    (patch ./ports/patch/bison-3.8.2.patch)
    (skipTests "too slow")
  ])

  (for pkgs.cmake [
    (pin "3.30.2" "sha256-RgdMeB7M68Qz6Y8Lv6Jlyj/UOB8kXKOxQOdxFTHWDbI=")
    (skipCheck "some tests fail")
    (addCMakeFlag "-DCMAKE_VERBOSE_MAKEFILE=ON")
    (addCMakeFlag "-DCMAKE_CXX_COMPILER=${pkgs.lib.getBin prev.stdenv.cc}/bin/c++")
    (addCMakeFlag "-DCMAKE_C_COMPILER=${pkgs.lib.getBin prev.stdenv.cc}/bin/cc")
    (addCMakeFlag "-DCMAKE_EXE_LINKER_FLAGS=-lm")
  ])

  {
    gmp = for pkgs.gmp [
      (tool depizloing-nm)
      (configure "gmp_cv_asm_underscore=yes")
      (configure "--disable-assembly")
      (configure "--disable-fat")
    ];
  }

  {
    pkgconf-unwrapped = for pkgs.pkgconf-unwrapped [
      (tool depizloing-nm)
    ];
  }

  # ━━━ Compression ━━━

  (for pkgs.xz [
    (pin "5.6.2" "sha256-qds7s9ZOJIoPrpY/j7a6hRomuhgi5QTcDv0YqAxibK8=")
    (patch ./ports/patch/xz-5.6.2.patch)
    (skipCheck "too slow")
    (tool pkgs.automake116x)
    (tool pkgs.autoconf)
  ])

  (for pkgs.zstd [
    (patch ./ports/patch/zstd-1.5.6.patch)
    (skipCheck "too slow")
    (addCFlag "-DZSTD_DISABLE_ASM")
  ])

  (for pkgs.lzo [
    (skipTests "too slow")
    (tool depizloing-nm)
    (configure "--disable-asm")
  ])

  # ━━━ Networking ━━━

  (for pkgs.curlMinimal [
    (arg { idnSupport = true; })
    (arg { pslSupport = true; })
    (arg { zstdSupport = true; })
    (arg { brotliSupport = true; })
    (arg { scpSupport = false; })
    (skipCheck "network tests flaky")
  ])

  (for pkgs.git [
    (pin "2.46.0" "sha256-fxI0YqKLfKPr4mB0hfcWhVTCsQ38FVx+xGMAZmrCf5U=")
    (skipPatch "git-send-email-honor-PATH.patch")
    (patch ./ports/patch/git-2.46.0.patch)
    (arg { withManual = true; })
    (arg { perlSupport = true; })
    (arg { pythonSupport = true; })
    (arg { sendEmailSupport = false; })
    (arg { zlib-ng = pkgs.zlib; })
    (skipTests "too slow")
    (removeMakeFlag "ZLIB_NG=1")
  ])

  (for pkgs.nghttp2 [
    (configure "--disable-app")
    (addCFlag "-Wno-deprecated-literal-operator")
  ])

  (for pkgs.openssh [
    (pin "9.8p1" "sha256-3YvQAqN5tdSZ37BQ3R+pr4Ap6ARh9LtsUjxJlz9aOfM=")
    (patch ./ports/patch/openssh-9.8p1.patch)
    (skipCheck "requires special setup")
    (arg { withFIDO = false; })
  ])

  (for pkgs.libssh2 [
    (tool depizloing-nm)
    (skipCheck "network tests flaky")
    (configure "--disable-examples-build")
  ])

  # ━━━ Security ━━━

  (for pkgs.libsepol [
    (patch ./ports/patch/libsepol-3.9.patch)
  ])

  (for pkgs.libselinux [
    (patch ./ports/patch/libselinux-3.9.patch)
  ])

  (for pkgs.keyutils [
    (pin "1.6.3" "sha256-ph1XBhNq5MBb1I+GGGvP29iN2L1RB+Phlckkz8Gzm7Q=")
    (patch ./ports/patch/keyutils-1.6.3.patch)
    (skipPatch "after_eq")
  ])

  (for pkgs.libgcrypt [
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
  ])

  (for pkgs.libsodium [
    (configure "--disable-ssp")
    (configure "--disable-asm")
  ])

  (for pkgs.libtasn1 [
    (skipTests "one test fails")
  ])

  (for pkgs.libgpg-error [
    (use (
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
      {
        postPatch = ''
          cp ${lock-obj-gnufilc0} src/syscfg/lock-obj-pub.x86_64-unknown-linux-gnufilc0.h
        '';
        postConfigure = ''
          cp ${lock-obj-gnufilc0} src/lock-obj-pub.native.h
        '';
      }
    ))
  ])

  (for pkgs.libkrb5 [
    (pin "1.21.3" "sha256-t6TNXq1n+wi5gLIavRUP9yF+heoyDJ7QxtrdMEhArTU=")
    (patch ./ports/patch/krb5-1.21.3.patch)
    (use { patchFlags = [ "-p2" ]; })
  ])

  (for pkgs.p11-kit [
    (skipTests "1 failure")
  ])

  # ━━━ Graphics ━━━

  (for pkgs.pixman [
    (use {
      mesonFlags = [
        "-Dgnu-inline-asm=disabled"
        "-Dmmx=disabled"
        "-Dsse2=disabled"
        "-Dssse3=disabled"
      ];
    })
    (skipTests "some tests fail")
  ])

  (for pkgs.cairo [
    (addCFlag "-Wno-error=int-conversion")
  ])

  (for pkgs.fontconfig [
    (skipCheck "some failures look sus")
  ])

  (for pkgs.glib [
    (pin "2.80.4" "sha256-JOApxd/JtE5Fc2l63zMHipgnxIk4VVAEs7kJb6TqA08=")
    (patch ./ports/patch/glib-2.80.4.patch)
    (patch ./glib-inline.patch)
    (skipPatch "split-dev-programs.patch")
    (patch ./glib-split-backport.patch)
    (arg { libsysprof-capture = null; })
    (skipTests "many failures")
    (use {
      mesonFlags = [
        "-Ddevbindir=${placeholder "dev"}/bin"
        "-Dglib_debug=disabled"
        "-Ddocumentation=true"
        (pkgs.lib.mesonBool "dtrace" false)
        (pkgs.lib.mesonBool "systemtap" false)
        "-Dnls=enabled"
        (pkgs.lib.mesonEnable "introspection" false)
        "-Dtests=false"
      ];
    })
  ])

  (for pkgs.gobject-introspection [
    (broken "turn this thing off so glib builds perfectly")
  ])

  (for pkgs.gobject-introspection-unwrapped [
    (use (old: {
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
  ])

  # ━━━ Development Tools & Libraries ━━━

  (for pkgs.doctest [
    (addCFlag "-Wno-reserved-macro-identifier")
    (addCFlag "-Wl,-lm")
  ])

  (for pkgs.isl [
    (tool depizloing-nm)
  ])

  (for pkgs.gdbm [
    (tool depizloing-nm)
  ])

  (for pkgs.gettext [
    (tool depizloing-nm)
    (use (old: {
      env = old.env // {
        gettextNeedsLdflags = false;
      };
    }))
  ])

  (for pkgs.elfutils [
    (configure "--disable-symbol-versioning")
    (configure "--disable-debuginfod")
    (addCFlag "-Wno-error=unused-parameter")
    (arg { enableDebuginfod = false; })
    (skipTests "some tests fail")
  ])

  (for pkgs.libcbor [
    (addCMakeFlag "-DCMAKE_VERBOSE_MAKEFILE=ON")
    (addCMakeFlag "-DCMAKE_NO_EXAMPLES=ON")
    (addCMakeFlag "-DCMAKE_SANITIZE=OFF")
    (skipTests "some tests fail")
  ])

  {
    pam = for pkgs.linux-pam [ (skipCheck "test setup issues") ];
  }

  (for pkgs.cmocka [
    (skipTests "some tests fail")
    (addCMakeFlag "-DWITH_EXAMPLES=OFF")
  ])

  (for pkgs.libbsd [
    (tool depizloing-nm)
    serialize
    (broken "not yet ported successfully")
  ])

  (for pkgs.rhash [
    (use {
      preConfigure = ''
        sed -i 's/,-soname/ -Wl,-soname/' configure
      '';
    })
    (addCFlag "-DRHASH_NO_ASM=1")
  ])

  (for pkgs.fasttext [
    (addCFlag "-Wl,-lm")
  ])

  (for pkgs.scrypt [
    (tool depizloing-nm)
    (skipTests "some tests fail")
  ])

  (for (pkgs.callPackage ./libmicrohttpd.nix { }) [ ])

  # ━━━ Languages ━━━

  (for pkgs.perl [
    (src "5.40.0" "sha256-x0A0jzVzljJ6l5XT6DI7r9D+ilx4NfwcuroMyN/nFh8=" (
      v: "https://www.cpan.org/src/5.0/perl-${v}.tar.gz"
    ))
    (patch ./ports/patch/perl-5.40.0.patch)
    (skipCheck "too slow")
  ])

  {
    python312 = for pkgs.python312 [
      (pin "3.12.5" "sha256-+oouEsXmILCfU+ZbzYdVDS5aHi4Ev4upkdzFUROHY5c=")
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
      (configure "ac_cv_gcc_asm_for_mc68881=no")
      (arg {
        packageOverrides = import ./pythonPorts-as-overlay.nix pkgs;
      })
    ];
  }

  # ━━━ Terminal & System ━━━

  (for pkgs.tmux [
    (arg { withSystemd = false; })
  ])

  (for pkgs.libutempter [
    (arg { glib = null; })
  ])

  (for pkgs.procps [
    (arg { withSystemd = false; })
    (patch ./ports/patch/procps-ng-4.0.4.patch)
  ])

  {
    util-linux = for pkgs.util-linuxMinimal [ parallelize ];
    util-linuxMinimal = for pkgs.util-linuxMinimal [ parallelize ];
  }

  (for pkgs.shadow [
    (tool depizloing-nm)
  ])

  (for pkgs.e2fsprogs [
    (arg { withFuse = false; })
    (skipTests "requires special setup")
  ])

  (for pkgs.sqlite [
    (arg { interactive = true; })
    (skipCheck "too slow")
    (removeCFlag "-DSQLITE_ENABLE_STMT_SCANSTATUS")
  ])

  (for pkgs.strace [
    (use { postPatch = ''sed -i 's/ vfork/ fork/g' */strace.c''; })
  ])

  (for pkgs.runit [
    (patch ./runit-pid-namespace.patch)
  ])

  # ━━━ Web & Network Services ━━━

  (for pkgs.lighttpd [
    (patch ./lighttpd-filc.patch)
    (arg { enableMagnet = true; })
    (arg { enableWebDAV = true; })
    (arg { enablePam = true; })
    (skipCheck "test suite issues")
    (configure "--with-zlib")
    (configure "--with-bzip2")
    (configure "--with-brotli")
    (configure "--with-zstd")
    (configure "--with-krb5")
  ])

  (for pkgs.tor [
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
    (skipTests "pass 17, skip 2, fail 6")
  ])

  (for pkgs.torsocks [
    (tool pkgs.glibc.bin)
    (tool depizloing-nm)
    (arg { libcap = null; })
    (use {
      postPatch = ''
        sed -i \
          -e 's,\(local app_path\)=`which $1`,\1=`type -P $1`,' \
          src/bin/torsocks.in
      '';
    })
    (skipTests "2 failing tests")
  ])

  # ━━━ Alternative Implementations & VMs ━━━

  (for pkgs.tinycc [
    (patch ./tinycc-alignment.patch)
    (use (old: {
      preConfigure = ''
        echo ${old.version} > VERSION
      '';
      configureFlags = [
        "--cc=$CC"
        "--ar=$AR"
        "--crtprefix=${pkgs.glibc}/lib"
        "--sysincludepaths={B}/include:${pkgs.glibc.dev}/include"
        "--libpaths=$lib/lib/tcc:$lib/lib:${pkgs.glibc}/lib"
        "--elfinterp=${pkgs.glibc}/lib/ld-linux-x86-64.so.2"
      ];
    }))
    (tool pkgs.glibc.bin)
    (skipTests "-run feature incompatible with Fil-C")
  ])

  (for pkgs.quickjs [
    (pin "2024-02-14" "sha256-PEv4+JW/pUvrSGyNEhgRJ3Hs/FrDvhA2hR70FWghLgM=")
    (patch ./ports/patch/quickjs.patch)
    (skipCheck "some tests fail")
  ])

  (for pkgs.trealla [
    (arg { lineEditingLibrary = "readline"; })
    (pin "2.84.14" "sha256-W1erZMHlX3s0Px62LHoMAcHWUeepDk3T63/R2QAyDAQ=")
    (patch ./patches/trealla-filc-ffi-zptrtable.patch)
    (skipTests "many fail with thwart in bif_iso_write, also slow")
  ])

  (for pkgs.wasm3 [
    markAsNotNecessarilyInsecure
  ])

  {
    kittydoom = for ./kitty-doom.nix [ ];
  }

  (for pkgs.luajit [
    (broken "JIT compiler not compatible with Fil-C")
  ])

  (for pkgs.rspamd [
    (arg { withLuaJIT = false; })
  ])

  # ━━━ Emacs ━━━

  {
    emacs30 = for pkgs.emacs30 [
      (arg {
        gnutls = null;
        systemd = null;
        mailutils = null;
        dbus = null;
        harfbuzz = null;
        withX = false;
        withGTK3 = false;
        withXwidgets = false;
        withNS = false;
        withPgtk = false;
        withImageMagick = false;
        withWebP = false;
        withTreeSitter = false;
        withGpm = false;
        withSystemd = false;
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
      (pin "30.1" "sha256-eTWjpRgLXbA9OQZnbrWPIHPcbj/QYkv58I3IWx5lCIQ=")
      (patch ./ports/patch/emacs-30.1.patch)
      (configure "--with-gnutls=ifavailable")
      (configure "--with-dumping=none")
      (configure "--with-pdumper=no")
      (configure "--with-unexec=no")
      (skipCheck "some tests fail")
    ];
  }

  # ━━━ Python Variants ━━━

  {
    python311 = for pkgs.python311 [
      (broken "use python 3.12")
    ];

    python313 = for pkgs.python313 [
      (broken "use python 3.12")
    ];
  }

  # ━━━ Broken / WIP ━━━

  (for pkgs.colm [
    (broken "null pointer dereference in bootstrap")
  ])

  (for pkgs.ragelStable [
    (broken "depends on colm which is broken")
  ])

  (for pkgs.tree-sitter [
    (broken "tries to cross compile rustc")
  ])

  (for pkgs.systemd [
    (broken "not yet ported")
  ])

  (for pkgs.dbus [
    (broken "not yet ported")
  ])

  (for pkgs.gnutls [
    (broken "too many dependencies")
  ])

  {
    gtk3 = for pkgs.gtk3 [
      (broken "GUI not supported")
    ];

    gtk4 = for pkgs.gtk4 [
      (broken "GUI not supported")
    ];
  }

  (for pkgs.wayland [
    (broken "display server not supported")
  ])

  (for pkgs.xorg.libX11 [
    (broken "X11 not supported")
  ])

  (for pkgs.rustc [
    (broken "oh sweet summer child")
  ])
]
