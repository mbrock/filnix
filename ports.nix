# Fil-C package ports - list-based structure
#
# Each port: (for pkgs.package [transforms...])
# Explicit names: { bash = for pkgs.bash [...]; }

{
  pkgs,
  prev,
  final,
}:
let
  inherit (import ./ports { inherit (pkgs) lib pkgs; })
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
    link
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
    astRewrite
    github
    gnu
    gnuTarGz
    ;

  # The build platform's guile, to compile Scheme modules to .go files
  # (the bytecode is the same). As an input it would propagate its
  # native libunistring and libgc onto the Fil-C link path, so only its
  # programs are exposed.
  guileForBuild = pkgs.runCommand "guile-for-build" { } ''
    mkdir -p $out/bin
    ln -s ${pkgs.buildPackages.guile_3_0}/bin/* $out/bin/
  '';

  # The Fil-C guile, for builds that must load Fil-C extensions or run
  # tests with it at build time. It runs on the build machine.
  filcGuileForBuild = pkgs.runCommand "filc-guile-for-build" { } ''
    mkdir -p $out/bin
    ln -s ${final.guile_3_0}/bin/* $out/bin/
  '';

  # Guile libraries whose tests load Fil-C code (their own extension or
  # a C library through the FFI) must run them with the Fil-C guile;
  # Nixpkgs' cross build would use the build platform's.
  guileTestsOnFilc = use (old: {
    preCheck = (old.preCheck or "") + ''
      export PATH=${final.guile_3_0}/bin:$PATH
      for f in pre-inst-env pre-inst-guile; do
        if [ -f $f ]; then
          substituteInPlace $f --replace-quiet \
            ${pkgs.buildPackages.guile_3_0}/bin/guile ${final.guile_3_0}/bin/guile
        fi
      done
    '';
    checkFlags = (old.checkFlags or [ ]) ++ [
      "GUILE=${final.guile_3_0}/bin/guile"
    ];
  });

  fftwPort = [
    (use (old: {
      patches = (old.patches or [ ]) ++ [
        ./patches/fftw-cpu-probe.patch
        ./patches/fftw-pointer-tags.patch
        ./patches/fftw-vector-load.patch
      ];
      nativeBuildInputs = builtins.filter (
        dep: !(pkgs.lib.hasInfix "gfortran" (dep.name or ""))
      ) old.nativeBuildInputs;
      # Nixpkgs adds LLVM's OpenMP when the compiler is Clang.
      buildInputs = builtins.filter (
        dep: !(pkgs.lib.hasInfix "openmp" (dep.name or ""))
      ) (old.buildInputs or [ ]);
      configureFlags =
        builtins.filter (
          f:
          !(builtins.elem f [
            "--enable-openmp"
            "--enable-avx512"
          ])
        ) old.configureFlags
        ++ [
          "--disable-fortran"
          "--disable-openmp"
          # Fil-C does not yet lower AVX-512 gather intrinsics.
          "--disable-avx512"
        ];
      doCheck = true;
    }))
  ];
in
[
  (import ./ports/pipewire-consumers.nix { inherit pkgs prev final; })
  (import ./ports/media.nix { inherit pkgs; })
  (import ./ports/tpm2.nix { inherit pkgs final; })

  # ━━━ Core Libraries ━━━

  {
    boost187 = for pkgs.boost187 [
      (patch ./ports/patch/boost-filc.patch)
      (patch ./patches/boost-context-feature.patch)
      (patch ./patches/boost-gdb-scripts.patch)
      (patch ./patches/boost-function-vtable-tag.patch)
      (patch ./patches/boost-test-execution-monitor.patch)
      # io_context's executor keeps its context pointer and flag bits in a
      # uintptr_t; the first use_service through a strand trapped.
      (patch ./patches/boost-asio-io-context-executor-pointer.patch)
      (use (old: {
        # error_code keeps its source_location pointer in a uintptr_t with
        # a flag bit, which drops the capability, and what() then trapped
        # (Boost.URL's parse errors in Nix). Keep no location instead.
        postPatch =
          (old.postPatch or "")
          + "\n"
          + ''
            substituteInPlace boost/system/detail/error_code.hpp --replace-fail \
              '( loc? reinterpret_cast<boost::uintptr_t>( loc ): 2 )' '2'
          '';
      }))
      (arg {
        # Match upstream pizlix: Context and Coroutine2 use ucontext.
        # The older Coroutine v1 library requires fcontext and is omitted.
        toolset = "clang";
        extraB2Args = [
          "context-impl=ucontext"
          "--without-coroutine"
        ];
      })
      (use {
        doCheck = true;
        checkPhase = ''
          runHook preCheck
          $CXX -std=c++17 -I. ${./tests/boost-context.cpp} \
            -Lstage/lib -Wl,-rpath,"$PWD/stage/lib" -lboost_context -lboost_json -pthread -o boost-check
          LD_LIBRARY_PATH="$PWD/stage/lib" ./boost-check
          $CXX -std=c++17 -I. ${./tests/boost-continuation.cpp} \
            -Lstage/lib -Wl,-rpath,"$PWD/stage/lib" -lboost_context -pthread -o continuation-check
          LD_LIBRARY_PATH="$PWD/stage/lib" ./continuation-check
          $CXX -std=c++17 -I. ${./tests/boost-asio.cpp} -pthread -o asio-check
          ./asio-check
          $CXX -std=c++17 -I. ${./tests/boost-error-code.cpp} -o error-code-check
          ./error-code-check
          # Boost.Test, both as the compiled library and header-only. The
          # module deliberately fails some cases, so compare its summary.
          $CXX -std=c++17 -I. -DBOOST_TEST_DYN_LINK ${./tests/boost-test.cpp} \
            -Lstage/lib -Wl,-rpath,"$PWD/stage/lib" -lboost_unit_test_framework -o boost-test-check
          sed 's|<boost/test/unit_test.hpp>|<boost/test/included/unit_test.hpp>|' \
            ${./tests/boost-test.cpp} > boost-test-included.cpp
          $CXX -std=c++17 -I. boost-test-included.cpp -o boost-test-included-check
          for check in ./boost-test-check ./boost-test-included-check; do
            status=0
            LD_LIBRARY_PATH="$PWD/stage/lib" $check --report_level=short \
              --color_output=no > boost-test.log 2>&1 || status=$?
            cat boost-test.log
            test "$status" = 201
            sed -n '/^Test module/,$p' boost-test.log | sed '/^$/d' \
              | diff -u ${./tests/boost-test.expected} -
          done
          runHook postCheck
        '';
      })
    ];
  }

  (
    let
      icuPort =
        icu: patches:
        for icu (
          map patch patches
          ++ [
            (tool pkgs.autoreconfHook)
            (tool pkgs.pkg-config)
            (use {
              # Nixpkgs unpacks into icu/source; the upstream tree has icu4c/source.
              patchFlags = [ "-p3" ];
              # ICU disables its upstream suite for cross builds; its "test" target
              # is just a directory. Exercise the real target libraries explicitly.
              doCheck = true;
              checkPhase = ''
                runHook preCheck
                $CXX ${./tests/icu.cpp} -Icommon -Ii18n -Llib \
                  -Wl,-rpath,"$PWD/lib" -licui18n -licuuc -licudata -o icu-check
                ./icu-check
                LD_LIBRARY_PATH="$PWD/lib" ./bin/uconv -V
                runHook postCheck
              '';
            })
          ]
        );
    in
    {
      icu76 = icuPort pkgs.icu76 [
        ./ports/patch/icu-76.1.patch
        ./patches/icu-cross-data.patch
      ];
      # The 78.3 refresh also applies cleanly to 77.1.
      icu77 = icuPort pkgs.icu77 [
        ./ports/patch/icu-78.3.patch
        ./patches/icu-cross-data.patch
      ];
      # Node.js, Ladybird and onlyoffice pin ICU 78.
      icu78 = icuPort pkgs.icu78 [
        ./ports/patch/icu-78.3.patch
        ./patches/icu-cross-data.patch
        ./patches/icu-pointer-toc-alias-data.patch
      ];
    }
  )

  {
    # `abseil-cpp` is an alias of this LTS branch, so both names get the port.
    abseil-cpp_202601 = for pkgs.abseil-cpp_202601 [
      # Upstream Fil-C's port: Status, Cord, Mutex and BitGenRef keep
      # pointers in integer words, which drops their capabilities.
      (patch ./ports/patch/abseil-cpp-20260107.1.patch)
      # [[clang::annotate]] in the public headers crashed FilPizlonator in
      # every consumer (protobuf, re2).
      (patch ./patches/abseil-cpp-no-refactor-annotate.patch)
    ];
  }

  (
    let
      protobufPort = sourcePatch: [
        # Tagged pointers in integer words, byte-wise swaps and inline
        # assembly in the C++ runtime (see the patch headers).
        (patch sourcePatch)
        # The Fil-C driver rewrites version scripts itself and cannot parse
        # `extern "C++" { ... }` blocks, so linking libprotobuf aborted.
        # The maps only hide non-protobuf symbols; skip them.
        (addCMakeFlag "-Dprotobuf_HAVE_LD_VERSION_SCRIPT=OFF")
        (use (old: {
          # Fil-C keeps a musttail call only when every pointer argument is
          # the caller's own argument. The table-driven parser advances
          # `ptr`, so field-to-field tail calls would add a frame per field;
          # PROTOBUF_TAILCALL false makes each field return to the parse
          # loop. Runs after Nixpkgs rewrites this #if for older versions.
          postPatch = (old.postPatch or "") + ''
            sed -i 's/^\(#if \w*(clang::musttail)\)/\1 \&\& !defined(__FILC__)/' \
              src/google/protobuf/port_def.inc
            grep -q '(clang::musttail) && !defined(__FILC__)' \
              src/google/protobuf/port_def.inc
          '';
        }))
      ];
      randomOrderingTest = [
        (use (old: {
          # Map salts its integer hash with the table address and rotates the
          # key by its low 6 bits; Fil-C's allocator returns tables with the
          # same low bits, so small maps iterate in a fixed order. Only this
          # statistical check of order randomization fails (4609 others pass
          # in 34.1); iteration order is unspecified either way.
          preCheck = (old.preCheck or "") + ''
            export GTEST_FILTER=-MapImplTest.RandomOrdering
          '';
        }))
      ];
    in
    {
      protobuf_34 = for pkgs.protobuf_34 (
        protobufPort ./patches/protobuf-34.1-filc.patch ++ randomOrderingTest
      );
      protobuf_33 = for pkgs.protobuf_33 (
        protobufPort ./patches/protobuf-33.6-filc.patch ++ randomOrderingTest
      );
      protobuf_21 = for pkgs.protobuf_21 (
        protobufPort ./patches/protobuf-21.12-filc.patch
      );
    }
  )

  {
    QuadProgpp = for pkgs.QuadProgpp [
      (patch ./patches/quadprogpp-link-math.patch)
    ];
  }

  (for pkgs.mpfr [
    (addCFlag "-DNO_ASM")
    (use (old: {
      postPatch = (old.postPatch or "") + ''
        # Fil-C aborts and allocation-size traps terminate with SIGTRAP.
        substituteInPlace tests/tests.c --replace-fail SIGABRT SIGTRAP
      '';
    }))
  ])

  (for pkgs.ada [
    # CMake's env emulator must not replace ctest's target path lookup.
    (patch ./patches/ada-cross-emulator-test.patch)
  ])

  (for pkgs.SDL_compat [
    # Keep the symbol loader out of line: SDL12_compat.c compiles in 30 s,
    # not 873 s (see the patch).
    (patch ./patches/sdl12-symbol-loader.patch)
    # sdl12-compat dlopens SDL2 by bare soname and relies on its RUNPATH,
    # which Fil-C's loader ignores for dlopen (see docs/filc-findings.md).
    # Name the libraries Nix selected, as the sdl2-compat port does for SDL3.
    # (The testver check also needs sdl2-compat's -Bsymbolic-functions.)
    (use (old: {
      postPatch = (old.postPatch or "") + ''
        substituteInPlace src/SDL12_compat.c \
          --replace-fail '"libSDL2-2.0.so.0"' '"${pkgs.lib.getLib final.sdl2-compat}/lib/libSDL2-2.0.so.0"' \
          --replace-fail '"libX11.so.6"' '"${pkgs.lib.getLib final.libx11}/lib/libX11.so.6"'
      '';
    }))
  ])

  (for pkgs.smpeg [
    # GTK 2 only serves the gtv demo player; SDL_mixer needs just the
    # library, so keep GTK 2 out of its closure.
    (use (old: {
      buildInputs = builtins.filter (
        dep: !(pkgs.lib.hasPrefix "gtk+" (dep.name or ""))
      ) old.buildInputs;
    }))
    (configure "--disable-gtk-player")
    # Nixpkgs links everything with -lX11, which GTK used to provide.
    (link final.libx11)
  ])

  (for pkgs.oniguruma [
    # Hash keys and values carry pointers; ordinary longs lose capabilities.
    (patch ./patches/oniguruma-pointer-data.patch)
  ])

  (for pkgs.zlib [
    (pin "1.3" "sha256-/wukwpIBPbwnUws6geH5qBPNOd4Byl4Pi/NVcC76WT4=")
    (patch ./ports/patch/zlib-1.3.patch)
  ])

  (for pkgs.zlib-ng [
    (pin "2.2.4" "sha256-pzNDwwk+XNxQ2Td5l8OBW4eP0RC/ZRHCx3WfKvuQ9aM=")
  ])

  {
    openssl = for ./ports/openssl.nix [ ];
    openssl-sarcasm = for ./ports/openssl-sarcasm.nix [ ];
  }

  (for pkgs.libev [
    # Replace inline asm mfence with __atomic_thread_fence (Fil-C can't handle inline asm)
    (use (attrs: {
      postPatch = (attrs.postPatch or "") + ''
        substituteInPlace ev.c \
          --replace-fail '#define ECB_MEMORY_FENCE         __asm__ __volatile__ ("mfence"   : : : "memory")' \
                         '#define ECB_MEMORY_FENCE         __atomic_thread_fence(__ATOMIC_SEQ_CST)' \
          --replace-fail '#define ECB_MEMORY_FENCE_ACQUIRE __asm__ __volatile__ (""         : : : "memory")' \
                         '#define ECB_MEMORY_FENCE_ACQUIRE __atomic_thread_fence(__ATOMIC_ACQUIRE)' \
          --replace-fail '#define ECB_MEMORY_FENCE_RELEASE __asm__ __volatile__ (""         : : : "memory")' \
                         '#define ECB_MEMORY_FENCE_RELEASE __atomic_thread_fence(__ATOMIC_RELEASE)'
      '';
    }))
  ])

  (for pkgs.libevent [
    (pin "2.1.12" "sha256-kubeG+nsF2Qo/SNnZ35hzv/C7hyxGQNQN6J9NGsEA7s=")
    (patch ./ports/patch/libevent-2.1.12.patch)
  ])

  # (for pkgs.attr [
  #   (pin "2.5.2" "sha256-Ob9nRS+kHQlIwhl2AQU/SLPXigKTiXNDMqYwmmgMbIc=")
  #   (patch ./ports/patch/attr-2.5.2.patch)
  # ])

  (for pkgs.expat [
    (pin "2.7.1" "sha256-NUVSVEuPmQEuUGL31XDsd/FLQSo/9cfY0NrmLA0hfDA=")
    (patch ./ports/patch/expat-2.7.1.patch)
  ])

  (for pkgs.nspr [
    # NSPR's x86_64 atomics are hand-written assembly (os_Linux_x86_64.s),
    # which Fil-C cannot assemble or check. Use the __sync builtins, as
    # NSPR already does on loongarch and or1k, and build no .s file.
    (patch ./patches/nspr-filc-atomics.patch)
    (addMakeFlag "PR_MD_ASFILES=")
    # PR_Accept(fd, NULL, ...) passed a length pointer with a null address,
    # which Linux ignores but Fil-C's accept rejects; pass no length.
    (patch ./patches/nspr-null-peer-address.patch)
    # PLArena keeps its addresses as integers and PL_ARENA_ALLOCATE cast
    # them back to pointers, which have no capability under Fil-C; NSS's
    # first arena allocation trapped. Derive them from the arena header.
    (patch ./patches/nspr-arena-pointer-provenance.patch)
    # Nixpkgs runs no tests; NSPR's own suite covers the atomics, threads
    # and loopback I/O (about 100 programs, a few minutes).
    (use {
      doCheck = true;
      checkPhase = ''
        runHook preCheck
        make -C pr/tests
        (cd pr/tests && ./runtests.sh "$PWD/../../dist")
        runHook postCheck
      '';
    })
  ])

  (for pkgs.nss [
    # The same integer-to-pointer cast as NSPR's arenas, in NSS's
    # arena-zeroing code.
    (patch ./patches/nss-arena-pointer-provenance.patch)
    # freebl's cpuid asm (cache line size for RSA) sets flags without a
    # "cc" clobber, which Fil-C rejects when it runs.
    (patch ./patches/nss-cpuid-cc-clobber.patch)
    # Saved digest state put the context at offset 12, so SHA-256's
    # function pointers lost their capabilities on the way through
    # PK11_CloneContext and every TLS 1.3 handshake trapped. Pad the header.
    (patch ./patches/nss-softoken-state-alignment.patch)
    # The TLS RSA key exchange swaps the real and fake premaster keys with
    # a constant-time XOR mask on the pointers, leaving bare integers.
    (patch ./patches/nss-ssl-cswap-symkey.patch)
    (use (old: {
      # NSS keys its x86-64 assembly and intrinsics (AES-NI, PCLMUL, SHA-NI,
      # AVX2 HACL*, the amd64 bignum and arcfour assembly) on
      # target_arch=="x64". Build for a target NSS does not know, which
      # selects the portable C code, and keep 64-bit words and __int128.
      buildPhase =
        builtins.replaceStrings
          [ "--target x64" ]
          [ "--target filc -Dhave_int128_support=1" ]
          old.buildPhase;
      # pk11_gtest and freebl_gtest initialize large std::vector test-vector
      # tables in one static constructor, which takes Fil-C's pipeline over
      # 20 minutes per file (SROA on the instrumented function). Skip them.
      postPatch = old.postPatch + ''
        sed -i -e '/gtests\/pk11_gtest\//d' -e '/gtests\/freebl_gtest\//d' nss.gyp
        # selfserv listens on the preferred loopback address for
        # "localhost" (::1 where IPv6 is up), but ssl.sh forced tstclnt to
        # IPv4 and could never connect; let tstclnt pick the same address.
        sed -i 's/tstclnt -4 /tstclnt /' tests/ssl/ssl.sh
        # dbtests requires the bigdb key dump to finish in under 5 seconds
        # of wall time; under Fil-C on a loaded builder it flakes. Keep the
        # check but allow a minute.
        sed -i 's/test ''${TIMEARRAY\[0\]} -lt 5/test ''${TIMEARRAY[0]} -lt 60/' \
          tests/dbtests/dbtests.sh
        grep -q 'TIMEARRAY\[0\]} -lt 60' tests/dbtests/dbtests.sh
      '';
      # Run a subset of NSS's QA suites against the build tree, before
      # installPhase rearranges the output: ciphers, certutil and the cert
      # database, SDR, CRMF, S/MIME, EC, and TLS coverage and client auth.
      # tools.sh (pk12util's cipher matrix, ~800 checks) passed locally but
      # takes over half an hour under Fil-C.
      doCheck = true;
      checkPhase = ''
        runHook preCheck
        (
          cd tests
          export HOST=localhost DOMSUF=localdomain USE_IP=TRUE IP_ADDRESS=localhost
          export DIST=$(dirname $out) OBJDIR=$(basename $out)
          export OS_ARCH=Linux DLL_PREFIX=lib DLL_SUFFIX=so BUILT_OPT=1 USE_64=1
          export TESTDIR=$TMPDIR/nss-tests NSS_CYCLES=standard
          export NSS_TESTS="cipher lowhash cert dbtests sdr crmf smime ec ssl"
          export NSS_SSL_TESTS=normal_normal NSS_SSL_RUN="cov auth"
          ./all.sh > $TMPDIR/nss-tests.log 2>&1 || true
        )
        sed -n '/^Tests summary/,$p' $TMPDIR/nss-tests.log
        if ! grep -q '^Failed: *0$' $TMPDIR/nss-tests.log; then
          grep -E 'FAILED|Failed' $TMPDIR/nss-tests.log | head -100
          exit 1
        fi
        runHook postCheck
      '';
    }))
  ])

  (for pkgs.libffi [
    (pin "3.8.0" "sha256-faPi2aFx6woDj1kuytP/K7JVDzSW2Hs7Ka0M9EMMDbQ=")
    (patch ./ports/patch/libffi-3.8.0.patch)
    # Closure handlers may write to their by-value arguments, which the
    # runtime passes in the read-only zargs() buffer (cffi's
    # test_callback_large_struct).
    (patch ./patches/libffi-closure-writable-args.patch)
    (tool pkgs.autoreconfHook)
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

  {
    libjpeg_turbo = (
      for pkgs.libjpeg_turbo [
        (patch ./ports/patch/libjpeg-turbo-3.0.1.patch)
        (addCMakeFlag "-DCMAKE_ASM_NASM_COMPILER=")
        (addCMakeFlag "-DCMAKE_SKIP_INSTALL_RPATH=ON")
        (arg { nasm = pkgs.hello; })
      ]
    );
  }

  (for pkgs.libxml2 [
    (patch ./ports/patch/libxml2-2.14.4.patch)
    (arg { pythonSupport = false; })
    (skipCheck "python tests fail")
  ])

  (for pkgs.libuv [
    (pin "1.51.0" "sha256-J+Vc9wg5E7+2gmynjN6d52R83tZI018kFj8tMbufUc0=")
    (patch ./ports/patch/libuv-1.51.0.patch)
    (skipTests "one test failed")
  ])

  (for pkgs.libxcrypt [
    (pin "4.4.36" "sha256-5eH0yu4KAd4q7ibjE4gH1tPKK45nKHlm0f79ZeH9iUM=")
    (patch ./ports/patch/libxcrypt-4.4.36.patch)
    (skipCheck "one test fails")
  ])

  # db and db5 are aliases of db53; override it so all three get the port.
  {
    db53 = for pkgs.db53 [
      # Private environments stored heap pointers in integer offsets and
      # mutex IDs; give them the offset-based shared-region layout.
      (patch ./patches/db-private-regions.patch)
      # db_load without -h opens a private environment.
      (use {
        doInstallCheck = true;
        installCheckPhase = ''
          printf 'key\nvalue\n' | "$bin/bin/db_load" -T -t btree t.db
          "$bin/bin/db_dump" -p t.db | grep -qx ' value'
        '';
      })
    ];
  }

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

  (for (pkgs.callPackage "${pkgs.path}/pkgs/development/libraries/libidn2"
    { }
  ) [ ])

  # Special case - libiconv comes from glibc in cross-compilation
  {
    libiconv = {
      pname = "libiconv";
      attrs = old: { };
      overrideArgs = { };
    };
  }

  (for pkgs.pth [
    # configure's makecontext probe passes a void (*)(void *) to
    # makecontext, which Clang rejects, so pth fell back to setjmp/longjmp
    # with a hand-patched jmp_buf stack pointer (sjljlx), which does not
    # exist for this libc. Fil-C implements makecontext/swapcontext, so
    # use pth's standard SUSv2 ucontext backend.
    (configure "--with-mctx-mth=mcsc")
    (configure "--with-mctx-dsp=sc")
    (configure "--with-mctx-stk=mc")
    (use {
      doCheck = true;
      # `make test` ignores test_std's exit status.
      checkPhase = ''
        runHook preCheck
        make test_std
        ./test_std
        runHook postCheck
      '';
    })
  ])

  # ━━━ Core Utilities ━━━

  (for pkgs.coreutils [
    (skipCheck "too slow in Fil-C")
  ])

  {
    bash = for pkgs.bash [
      (arg { interactive = true; })
      # unwind_protect saves jmp_bufs in a misaligned buffer, losing their
      # capabilities: `bash -c 'set -e; false'` crashed.
      (patch ./ports/patch/bash-5.3.patch)
      (skipCheck "interactive mode issues")
    ];

    bashNonInteractive = for pkgs.bash [
      (arg { interactive = false; })
      # unwind_protect saves jmp_bufs in a misaligned buffer, losing their
      # capabilities: `bash -c 'set -e; false'` crashed.
      (patch ./ports/patch/bash-5.3.patch)
      (skipCheck "test issues")
    ];
  }

  (for pkgs.busybox [
    (use {
      enableStatic = false;
      enableAppletSymlinks = false;
      enableMinimal = false;
    })
    # The Makefile calls plain `cc` (filcc has no target prefix), and the
    # build platform's compiler, there for HOSTCC, comes first on PATH: the
    # result was a native busybox. Name the Fil-C compiler explicitly.
    (use (old: {
      makeFlags = (old.makeFlags or [ ]) ++ [
        "CC=${final.stdenv.cc}/bin/cc"
        # Partial links (-r) of built-in.o: the Fil-C driver adds its own
        # main even there, which then clashes in the final link.
        "LD=${final.stdenv.cc.bintools}/bin/ld"
      ];
    }))
    # Fil-C's libc has no vfork; busybox vforks only to exec or exit.
    (addCFlag "-Dvfork=fork")
    # Under clang, busybox writes its const global pointers through an asm
    # statement that launders the pointer, which Fil-C refuses. Make those
    # globals plain variables (busybox's documented switch) and take the
    # ordinary assignment path.
    (addCFlag "-DBB_GLOBAL_CONST=")
    (use (old: {
      postPatch =
        (old.postPatch or "")
        + "\n"
        + ''
          substituteInPlace include/libbb.h libbb/const_hack.c --replace-fail \
            '#if defined(__clang_major__) && __clang_major__ >= 9' \
            '#if defined(__clang_major__) && __clang_major__ >= 9 && !defined(__FILC__)'
          # printf %s passes the string to printf as a long long when the sizes
          # match, which drops its capability; take the char * path instead.
          substituteInPlace coreutils/printf.c --replace-fail \
            'if (sizeof(argument) == sizeof(llv)) {' 'if (0) {'
        '';
    }))
    # nixpkgs' separate debug info adds -Wa,--compress-debug-sections, which
    # Fil-C's assembler rejects, and busybox skips the preConfigure hook
    # removeCFlag relies on.
    (use { separateDebugInfo = false; })
  ])

  (for pkgs.diffutils [
    (pin "3.10" "sha256-kOXpPMck5OvhLt6A3xY0Bjx6hVaSaFkZv+YLVWyb0J4=")
    # Nixpkgs' gnulib test fixes target 3.12.
    (skipPatch "gnulib-float-h-tests-port-to-C23-PowerPC-GCC.patch")
    (skipPatch "musl-llvm.patch")
    (patch ./ports/patch/diffutils-3.10.patch)
    (tool pkgs.perl)
    (use { postPatch = "patchShebangs man/help2man"; })
    (skipTests "too slow")
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

  (for pkgs.a2ps [
    (use (old: {
      # gnulib's old obstack.h aligns pointers relative to (char *) 0,
      # which drops their capabilities; align relative to the chunk.
      postPatch = (old.postPatch or "") + ''
        substituteInPlace lib/obstack.h --replace-fail \
          '__BPTR_ALIGN (sizeof (ptrdiff_t) < sizeof (void *) ? (B) : (char *) 0,' \
          '__BPTR_ALIGN ((B),'
        substituteInPlace tests/backup.tst tests/styles.tst \
          --replace-quiet /bin/rm rm
      '';
      doCheck = true;
      preCheck = "patchShebangs contrib tests";
    }))
  ])

  {
    # Pointers that Guile keeps as scm_t_bits words, weak tables on
    # FUGC, continuations without C stack copying: see docs/guile.md.
    guile_3_0 = for pkgs.guile_3_0 [
      (patch ./ports/patch/guile-3.0.11.patch)
      # Nixpkgs' cross-build fix is already in 3.0.11.
      (skipPatch "c117f8edc471d3362043d88959d73c6a37e7e1e9")
      # Guile's JIT emits machine code.
      (configure "--disable-jit")
      (use (old: {
        depsBuildBuild = [ pkgs.stdenv.cc ];
        nativeBuildInputs = old.nativeBuildInputs ++ [ guileForBuild ];
        # A smoke test of the installed interpreter. The test suite is
        # run by hand (docs/guile.md); like Nixpkgs, the build skips it.
        doInstallCheck = true;
        installCheckPhase = ''
          runHook preInstallCheck
          $out/bin/guile -c '
            (use-modules (ice-9 match) (srfi srfi-1) (ice-9 format))
            (define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
            (unless (= (fib 20) 6765) (exit 1))
            (unless (equal? (match (list 1 2 3) ((a . b) b)) (list 2 3)) (exit 1))
            (gc)
            (unless (= (fold + 0 (iota 100000)) 4999950000) (exit 1))
            (unless (string=? (format #f "~a-~s" 1 "x") "1-\"x\"") (exit 1))
            (unless (= 3 (call/cc (lambda (k) (+ 1 (k 3))))) (exit 1))
            (display "guile ok\n")'
          runHook postInstallCheck
        '';
      }))
    ];

    # Nixpkgs lists guile only as a host input, so configure finds no
    # guile to compile the modules with. The build platform's guile
    # cannot load Fibers' Fil-C extension, which configure checks for,
    # so use the Fil-C guile itself: it runs on the build machine.
    gnu-shepherd = for pkgs.gnu-shepherd [
      (use (old: {
        nativeBuildInputs = old.nativeBuildInputs ++ [ filcGuileForBuild ];
      }))
    ];

    # Pure Guile. As with gnu-shepherd, configure needs a guile, and its
    # tests run with the Fil-C one.
    lilypond = for pkgs.lilypond [
      # The default TeX is built from the host package set, since it is
      # a derived value that splicing does not reach; it only runs at
      # build time.
      (arg {
        # WIP: the Fil-C ghostscript-with-X fails configure (its -lz check
        # links the build platform's zlib), so the lilypond wrapper puts
        # the build platform's gs on PATH for PDF output.
        ghostscript = pkgs.buildPackages.ghostscript;
        tex = pkgs.buildPackages.texliveSmall.withPackages (
          ps: with ps; [
            epsf
            fontinst
            fontware
            lh
            metafont
          ]
        );
      })
      (use (old: {
        # Nixpkgs lists guile only as a build tool. LilyPond links
        # libguile, and the build runs the Fil-C lilypond (it runs on
        # the build machine) to compile its Scheme files.
        nativeBuildInputs =
          builtins.filter (
            d: !(pkgs.lib.hasPrefix "guile" (d.name or ""))
          ) old.nativeBuildInputs
          ++ [ guileForBuild ];
        buildInputs = old.buildInputs ++ [ final.guile_3_0 ];
        # configure sets CROSS=yes, which drops the rules that run the
        # programs (help2man, lilypond itself) but not the targets that
        # need them. Fil-C programs run on the build machine.
        makeFlags = (old.makeFlags or [ ]) ++ [ "CROSS=no" ];
        # handle_broken_dependencies () replaces the system's
        # all-elements Grob_array, so the old one can be collected and
        # deleted while this function still reads it through a reference
        # (a use-after-free that Fil-C stops in 19 regression tests).
        # Keep its SCM alive until the end.
        postPatch = (old.postPatch or "") + ''
          substituteInPlace lily/system.cc \
            --replace-fail \
              'std::vector<Grob *> &all_elts = all_elements ()->array_reference ();' \
              'SCM all_elts_scm = get_object (this, "all-elements");
          std::vector<Grob *> &all_elts = all_elements ()->array_reference ();' \
            --replace-fail \
              'debug_output (_f ("Element count %zu", count + all_elts.size ()) + "\n");' \
              'debug_output (_f ("Element count %zu", count + all_elts.size ()) + "\n");
          scm_remember_upto_here_1 (all_elts_scm);'
        '';
      }))
    ];

    guile-zlib = for pkgs.guile-zlib [ guileTestsOnFilc ];
    guile-gcrypt = for pkgs.guile-gcrypt [
      # Otherwise configure finds the build platform's libgcrypt-config
      # and records that libgcrypt for the FFI.
      (configure "--with-libgcrypt-prefix=${final.libgcrypt.dev}")
      (configure "--with-libgcrypt-libdir=${pkgs.lib.getLib final.libgcrypt}/lib")
      guileTestsOnFilc
    ];
    guile-lzlib = for pkgs.guile-lzlib [
      # configure finds liblz by running ldd on a test program, which
      # does not work for a Fil-C program.
      (configure "guile_cv_liblz_libdir=${final.lzlib.out}/lib/liblz.so")
      guileTestsOnFilc
    ];
    guile-zstd = for pkgs.guile-zstd [ guileTestsOnFilc ];
    guile-lzma = for pkgs.guile-lzma [ guileTestsOnFilc ];
    guile-sqlite3 = for pkgs.guile-sqlite3 [ guileTestsOnFilc ];
    guile-git = for pkgs.guile-git [
      guileTestsOnFilc
      # Connecting to a socket that never accepts times out with a
      # GITERR_OS error instead of GITERR_NET with the Fil-C libgit2.
      (use (old: {
        preCheck = (old.preCheck or "") + ''
          substituteInPlace tests/clone.scm --replace-fail \
            '(test-equal "clone beyond timeout"' \
            '(test-skip 1) (test-equal "clone beyond timeout"'
        '';
      }))
    ];
    guile-avahi = for pkgs.guile-avahi [
      # Clang reports an unused static function that GCC does not.
      (addCFlag "-Wno-error=unused-function")
      guileTestsOnFilc
    ];

    guix = for pkgs.guix [
      # configure takes libgcrypt from the build platform's
      # libgcrypt-config otherwise; the path also ends up in
      # guix/config.scm for the FFI.
      (configure "--with-libgcrypt-prefix=${final.libgcrypt.dev}")
      (configure "--with-libgcrypt-libdir=${pkgs.lib.getLib final.libgcrypt}/lib")
      (use (old: {
        # graphviz (for documentation figures) fails to build natively at
        # this Nixpkgs pin (its X variant installs no vimdot), so use the
        # variant without X. slirp4netns (for container networking) needs
        # libseccomp, and the Fil-C runtime does not support the seccomp
        # system call.
        nativeBuildInputs =
          builtins.filter (
            d:
            !(builtins.elem (d.pname or "") [
              "graphviz"
              "slirp4netns"
            ])
          ) old.nativeBuildInputs
          ++ [ pkgs.buildPackages.graphviz-nox ];
        propagatedBuildInputs = builtins.filter (
          d: (d.pname or "") != "slirp4netns"
        ) old.propagatedBuildInputs;
        # The build-time tools (guile, makeinfo for the translated
        # manuals) need a UTF-8 locale; the native build gets it from
        # glibcLocales' hook, which does not apply here.
        LOCALE_ARCHIVE = "${pkgs.buildPackages.glibcLocales}/lib/locale/locale-archive";
        LC_ALL = "C.UTF-8";
        # The wrapper records $GUILE_LOAD_PATH, which also holds the build
        # platform's Guile libraries (used to compile the modules); their
        # FFI bindings point at native libraries, which a Fil-C process
        # cannot load. Keep only the host's.
        preInstall = (old.preInstall or "") + ''
          hostOnly() { printf %s "$1" | tr : '\n' | grep -- -gnufilc0- | paste -sd: -; }
          export GUILE_LOAD_PATH=$(hostOnly "$GUILE_LOAD_PATH")
          export GUILE_LOAD_COMPILED_PATH=$(hostOnly "$GUILE_LOAD_COMPILED_PATH")
        '';
      }))
    ];

    mcron = for pkgs.mcron [
      (use (old: {
        nativeBuildInputs = old.nativeBuildInputs ++ [ filcGuileForBuild ];
      }))
    ];

    mailutils = for pkgs.mailutils [
      # Configure finds GNU gss unusable for Fil-C.
      (removeConfigureFlag "--with-gssapi")
      (use (old: {
        # guile-config runs an unprefixed pkg-config; give it the host's,
        # so that it reports the Fil-C guile.
        nativeBuildInputs = old.nativeBuildInputs ++ [
          guileForBuild
          (pkgs.writeShellScriptBin "pkg-config" ''exec "$PKG_CONFIG" "$@"'')
        ];
        # The Guile binding tests load the Fil-C libmu_scm, so they need
        # the Fil-C guile (it runs on the build machine).
        preCheck = (old.preCheck or "") + ''
          export PATH=${final.guile_3_0}/bin:$PATH
        '';
        # Out-of-bounds reads that Fil-C stops: imap4d's LIST reads
        # ref[-1] for an empty reference; in test helpers, a memmove from
        # the wrong offset, a loop that tests the output pointer instead
        # of the input, and argv[i][len - 1] on an empty argument.
        postPatch = (old.postPatch or "") + ''
          substituteInPlace imap4d/list.c \
            --replace-fail "if (ref[refinfo.reflen-1] != pfx->delim" \
                           "if (refinfo.reflen > 0 && ref[refinfo.reflen-1] != pfx->delim"
          # Its word-wrapping stream kept writing after a failed flush
          # (EPIPE when mail --version is piped into sed, which quits
          # after the first line), past the end of its line buffer.
          substituteInPlace libmailutils/stream/wordwrap.c --replace-fail \
            "	_wordwrap_flush_line (str, iptr[n]);" \
            "	{ int rc = _wordwrap_flush_line (str, iptr[n]); if (rc) return rc; }"
          substituteInPlace testsuite/cwdrepl.c \
            --replace-fail 'size_t rest = n - start;' 'size_t rest = n - off;'
          substituteInPlace libmailutils/tests/encode2047.c \
            --replace-fail 'for (p = buf; *p;)' 'for (p = buf; *buf;)'
          substituteInPlace libmailutils/tests/tesh.c \
            --replace-fail "if (argv[i][len - 1] == ';')" \
                           "if (len > 0 && argv[i][len - 1] == ';')"
        '';
      }))
    ];
  }

  (for pkgs.gnugrep [
    (pin "3.11" "sha256-HbKu3eidDepCsW2VKPiUyNFdrk4ZC1muzHj1qVEnbqs=")
    # Nixpkgs' gnulib test fix targets 3.12.
    (skipPatch "gnulib-float-h-tests-port-to-C23-PowerPC-GCC.patch")
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
    (skipPatch "acl-2.4.0-name-conflicts.patch") # also part of the port
    (arg { aclSupport = false; })
  ])

  (for pkgs.gnum4 [
    (pin "1.4.19" "sha256-swapHA/ZO8QoDPwumMt6s5gf91oYe+oyk4EfRSyJqMg=")
    (patch ./ports/patch/m4-1.4.19.patch)
  ])

  # ━━━ Build Tools ━━━

  (for pkgs.bison [
    (pin "3.8.2" "sha256-BsnhO99+sk1M62tZIFpPZ8LH5yExGWREMP6C+9FKCrs=")
    (patch ./ports/patch/bison-3.8.2.patch)
    (skipTests "too slow")
  ])

  (for pkgs.cmake [
    # No Fil-C source patch; Nixpkgs 26.05's patches only apply to 4.x.
    (skipCheck "some tests fail")
    (addCMakeFlag "-DCMAKE_VERBOSE_MAKEFILE=ON")
    (addCMakeFlag "-DCMAKE_CXX_COMPILER=${pkgs.lib.getBin prev.stdenv.cc}/bin/c++")
    (addCMakeFlag "-DCMAKE_C_COMPILER=${pkgs.lib.getBin prev.stdenv.cc}/bin/cc")
    (addCMakeFlag "-DCMAKE_EXE_LINKER_FLAGS=-lm")
  ])

  # Only the C API is used. Avoid the unsupported target Fortran compiler
  # and OpenMP runtime. The other precisions are overrides of this one.
  { fftw = for pkgs.fftw fftwPort; }

  (for pkgs.v4l-utils [
    # The BPF decoders are compiled by a clang for the BPF target.
    (arg { withBPF = false; })
  ])

  {
    ffmpeg-headless = for pkgs.ffmpeg-headless [
      # Upstream Fil-C's FFmpeg 8.0.1 port applies unchanged to 8.1.
      (patch ./ports/patch/ffmpeg-8.0.1.patch)
      (use (old: {
        # 8.1 keeps the log callback in an atomic_uintptr_t, which drops the
        # function pointer's capability; every av_log call trapped.
        postPatch =
          (old.postPatch or "")
          + "\n"
          + ''
            substituteInPlace libavutil/log.c \
              --replace-fail \
                'static atomic_uintptr_t av_log_callback = (uintptr_t)av_log_default_callback;' \
                'static void (*_Atomic av_log_callback)(void*, int, const char*, va_list) = av_log_default_callback;' \
              --replace-fail \
                'atomic_store_explicit(&av_log_callback, (uintptr_t)callback,' \
                'atomic_store_explicit(&av_log_callback, callback,'
            # flashsv2 rebased block pointers from one buffer into another
            # with a pointer difference, keeping the first buffer's bounds.
            substituteInPlace libavcodec/flashsv2enc.c --replace-fail \
              's->key_blocks[i].enc += (s->keybuffer - s->encbuffer);' \
              's->key_blocks[i].enc = s->keybuffer + (s->key_blocks[i].enc - s->encbuffer);'
          '';
      }))
      # Hand-written x86 assembly and inline assembly; upstream builds the
      # same way.
      (configure "--disable-asm")
      # CUDA kernels would be compiled by a clang for the NVPTX target.
      (arg {
        withCudaLLVM = false;
        withNvcodec = false;
        # x265 builds its 10/12-bit variants with GCC, and vid.stab uses
        # OpenMP; neither toolchain targets Fil-C.
        withX265 = false;
        withVidStab = false;
      })
    ];
  }

  {
    libgbm = for pkgs.libgbm [
      # Mesa's BLAKE3 has hand-written x86-64 assembly; use its C versions, as
      # Mesa itself does for x32.
      (use (old: {
        postPatch =
          (old.postPatch or "")
          + "\n"
          + ''
            substituteInPlace src/util/blake3/meson.build \
              --replace-fail "elif cc.sizeof('void *') == 4" "elif true"
          '';
      }))
    ];
  }

  (for pkgs.imlib2 [
    # Hand-written AMD64 blending assembly.
    (configure "--enable-amd64=no")
  ])

  (for pkgs.libvpx [
    # Build without the x86 assembly and intrinsics dispatch.
    (removeConfigureFlag "--target=x86_64-linux-gcc")
    (configure "--target=generic-gnu")
    (arg { runtimeCpuDetectSupport = false; })
  ])

  (for pkgs.libgit2 [
    (patch ./patches/libgit2-configmap-cache-clear.patch)
    # xdiff adds src/util as a SYSTEM include directory, which then comes
    # after the wrapper's -isystem for Fil-C glibc, whose obsolete
    # <regexp.h> stub shadows libgit2's own "regexp.h".
    (use (old: {
      postPatch =
        (old.postPatch or "")
        + "\n"
        + ''
          substituteInPlace deps/xdiff/CMakeLists.txt \
            --replace-fail "target_include_directories(xdiff SYSTEM PRIVATE" \
              "target_include_directories(xdiff PRIVATE"
        '';
    }))
  ])

  # Video codecs: build the portable C code paths, without hand-written
  # assembly or intrinsics dispatch.
  (for pkgs.x264 [ (configure "--disable-asm") ])
  (for pkgs.svt-av1 [
    (removeCMakeFlag "-DSVT_AV1_LTO=ON")
    (addCMakeFlag "-DCOMPILE_C_ONLY=ON")
  ])
  (for pkgs.libaom [ (addCMakeFlag "-DAOM_TARGET_CPU=generic") ])

  (for pkgs.onetbb [
    # tbbmalloc carves objects out of raw mmap chunks, so its pointers carry
    # no capability; TBB falls back to malloc without it.
    (addCMakeFlag "-DTBBMALLOC_BUILD=OFF")
    # - queuing_rw_mutex tags its queue pointers in std::atomic<uintptr_t>;
    #   keep them in std::atomic<char*> and set the tag by pointer arithmetic.
    # - Clang claims __GNUC__ 4, so TBB picked a "lock; notb" fence and
    #   stmxcsr/fstcw for the FPU state, inline asm with memory operands
    #   that Fil-C refuses; use std::atomic_thread_fence and <fenv.h>.
    (patch ./patches/onetbb-fil-c.patch)
    (use (old: {
      postPatch =
        (old.postPatch or "")
        + "\n"
        + ''
          # The tests use doctest, whose signal handling needs sigaltstack.
          sed -i '/#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN/a #define DOCTEST_CONFIG_NO_POSIX_SIGNALS' \
            test/common/test.h
          grep -q DOCTEST_CONFIG_NO_POSIX_SIGNALS test/common/test.h
        '';
      disabledTests = (old.disabledTests or [ ]) ++ [
        # They expect allocations of nearly 2^64 bytes to throw bad_alloc;
        # Fil-C stops the program instead.
        "test_allocators"
        "conformance_allocators"
        # Its own cpuid inline asm does not declare the clobbered ecx.
        "test_mutex"
      ];
      # Not usable yet: the task scheduler and collaborative_call_once
      # still keep pointers in integers and trap in most tests, and
      # test_eh_algorithms spins. Marked unsupported so that dependents
      # (libblake3's useTBB, ...) leave it out.
      meta = old.meta // {
        badPlatforms = (old.meta.badPlatforms or [ ]) ++ [
          prev.stdenv.hostPlatform.system
        ];
      };
    }))
  ])

  (for pkgs.libblake3 [ (addCMakeFlag "-DBLAKE3_SIMD_TYPE=none") ])

  (for pkgs.wavpack [ (configure "--disable-asm") ])

  # Its MMX/SSE routines are yasm assembly, which Fil-C cannot link.
  (for pkgs.xvidcore [ (configure "--disable-assembly") ])

  (for pkgs.libopus [
    (patch ./ports/patch/opus-1.5.2.patch)
    # Without the x86 intrinsics and their run-time CPU dispatch.
    (addMesonFlag "-Dintrinsics=disabled")
    (addMesonFlag "-Drtcd=disabled")
  ])

  (for pkgs.zix [ (patch ./patches/zix-ring-mlock.patch) ])

  (for pkgs.libopenmpt [
    (patch ./patches/libopenmpt-x87-control-word.patch)
    # Found by Fil-C: a use-after-free when libc++'s codecvt returns
    # partial, as it does for non-ASCII text in the C locale.
    (patch ./patches/libopenmpt-codecvt-partial.patch)
  ])

  (for pkgs.libpulseaudio [
    # pa_atomic_ptr_t kept pointers in a uintptr_t, dropping their
    # capabilities (pa_once's mutex came back null).
    (patch ./patches/pulseaudio-atomic-ptr.patch)
    (use (old: {
      # PA_WARN_REFERENCE emits .gnu.warning sections as module asm, which
      # FilPizlonator does not accept; drop the link-time warnings.
      postPatch = (old.postPatch or "") + ''
        substituteInPlace src/pulsecore/macro.h --replace-fail \
          '#if defined(__GNUC__) && defined(__ELF__)' '#if 0'
        # Report no MMX/SSE, so the inline-asm mixing and volume routines
        # stay unused.
        substituteInPlace src/pulsecore/cpu-x86.c --replace-fail \
          '/* get standard level */' 'return;'
        # Fil-C's abort() raises SIGTRAP, and SIGBUS handlers are refused.
        sed -i 's/\(test_replace_fail_[0-9]\), SIGABRT/\1, SIGTRAP/' \
          src/tests/core-util-test.c
        sed -i "/\[ 'sigbus-test', 'sigbus-test.c',/,+1d" src/tests/meson.build
      '';
      # The mix and remap benchmarks outlast their 120 s check timeout.
      env = (old.env or { }) // {
        CK_TIMEOUT_MULTIPLIER = "5";
      };
    }))
  ])

  (for pkgs.libcamera [
    # LTTng-UST tracepoints; the tracer's own tests exercise signal and
    # namespace machinery Fil-C does not provide.
    (arg {
      withTracing = false;
      # jinja2, PyYAML and ply run on the build Python (3.13); the Fil-C
      # set is for the ported 3.12, so meson could not import jinja2.
      python3Packages = pkgs.python3Packages;
    })
    # The experimental Python bindings would need the Fil-C Python.
    (addMesonFlag "-Dpycamera=disabled")
    (patch ./patches/libcamera-no-dynamic.patch)
  ])

  (for pkgs.polkit [
    # polkit's hand-written get_type functions keep the GType in a
    # volatile gsize, but GType is a pointer in Fil-C's GLib; use a GType
    # with g_once_init_{enter,leave}_pointer (GLib 2.80).
    (patch ./patches/polkit-pointer-gtype.patch)
    # The runaway-script test needs asynchronous pthread_cancel, which
    # Fil-C does not deliver (SIGCANCEL is reserved by the runtime); it
    # hung forever. Under Fil-C a runaway rules script is not killed.
    (patch ./patches/polkit-filc-no-runaway-test.patch)
    # gtk-doc generates an unported GType scanner; GIR generation stays on.
    (removeMesonFlag "-Dgtk_doc=true")
    (addMesonFlag "-Dgtk_doc=false")
  ])

  (for pkgs.libgudev [
    # The tests preload umockdev, whose Vala-generated code assumes integer
    # GTypes, and LD_PRELOAD interposition does not apply to Fil-C symbols.
    (use (old: {
      doCheck = false;
      # GType is a pointer in Fil-C's GLib.
      postPatch = (old.postPatch or "") + ''
        substituteInPlace gudev/gudevenumtypes.c.template \
          --replace-fail 'static gsize static_g_define_type_id' \
            'static GType static_g_define_type_id' \
          --replace-fail 'g_once_init_enter (' 'g_once_init_enter_pointer (' \
          --replace-fail 'g_once_init_leave (' 'g_once_init_leave_pointer ('
        # Clang has no -export-dynamic driver flag (GCC passes it to ld).
        substituteInPlace gudev/meson.build \
          --replace-fail "'-export-dynamic'," "'-Wl,--export-dynamic',"
      '';
    }))
  ])

  (for pkgs.libical [
    # The libical-glib install check runs PyGObject on the build platform,
    # which the Fil-C Python port's package overrides (pyports.nix) also
    # reach and break.
    (use {
      doInstallCheck = false;
      nativeInstallCheckInputs = [ ];
    })
  ])

  (for pkgs.libshout [
    # configure only finds -lssl, but libshout also calls libcrypto directly.
    (addCFlag "-Wl,-lcrypto")
  ])

  (for pkgs.ell [
    (patch ./patches/ell-no-debug-section.patch)
    # test-ecdh wraps l_getrandom with ld --wrap, whose __real_ symbol
    # Fil-C does not rename.
    (skipCheck "ld --wrap")
  ])

  (for pkgs.bluez [
    # BlueZ builds against the copy of ELL's headers in its tarball.
    (patch ./patches/ell-no-debug-section.patch)
    (patch ./patches/bluez-no-debug-section.patch)
    # The MIDI profile stores pointers into ALSA's packed snd_seq_ev_ext,
    # at a misaligned offset where Fil-C cannot keep a capability.
    (removeConfigureFlag "--enable-midi")
    (configure "--disable-midi")
    (use (old: {
      # The installed test scripts run on Fil-C Python with its dbus-python
      # and PyGObject. The build Python's wrapPython would give them the
      # build interpreter and search its own, empty, site-packages layout.
      nativeBuildInputs = map (
        p:
        if pkgs.lib.hasPrefix "wrap-python-hook" (p.name or "") then
          final.python3Packages.wrapPython
        else
          p
      ) old.nativeBuildInputs;
    }))
  ])

  (for pkgs.liburcu [
    # Use compiler atomics instead of the x86 inline assembly ones.
    (configure "--enable-compiler-atomic-builtins")
    # The x86 header still used inline-assembly barriers ("lock; addl"),
    # which Fil-C rejects when they run, and the memb flavor probed
    # membarrier(2), which Fil-C refuses by stopping the program. Use the
    # generic builtin barriers and the existing no-membarrier fallback.
    # With that, the unit tests (674) pass and run again.
    (patch ./patches/liburcu-filc.patch)
  ])

  (for pkgs.lttng-ust [
    # With liburcu's compiler-builtin atomics, uatomic_or on the tagged
    # node->next pointer does not compile; set the flag with a CAS loop.
    (patch ./patches/lttng-ust-rculfhash-removed-flag.patch)
    # Fil-C has no dl_iterate_phdr, which the base-address statedump
    # uses to list loaded objects; skip that statedump.
    (patch ./patches/lttng-ust-no-dl-iterate-phdr.patch)
    # liblttng-ust-common's constructor probed membarrier(2), which Fil-C
    # refuses by stopping the program; use the existing smp_mb fallback.
    (patch ./patches/lttng-ust-no-membarrier.patch)
    # Fil-C has no __start_/__stop_ section symbols, and the weak
    # references in <lttng/tracepoint.h> crashed every instrumented
    # program at startup; register each tracepoint from a constructor.
    (patch ./patches/lttng-ust-tracepoint-ctor-registration.patch)
    # libnuma's numa_preferred() trips a bounds check in Fil-C's
    # get_mempolicy wrapper (docs/filc-findings.md), which the ring buffer
    # calls for every channel.
    (configure "--disable-numa")
  ])

  (for pkgs.mbedtls [
    (patch ./patches/mbedtls-test-cli-crt-ec-der-len.patch)
    # AES-NI, PadLock and bignum inline assembly pass pointers to asm.
    (use (old: {
      postPatch =
        (old.postPatch or "")
        + "\n"
        + ''
          for option in MBEDTLS_AESNI_C MBEDTLS_PADLOCK_C MBEDTLS_HAVE_ASM; do
            ${pkgs.python3}/bin/python3 scripts/config.py unset $option
          done
        '';
    }))
  ])

  (for pkgs.libpq [
    # Nixpkgs uses -flto with Clang to drop unused pg_config paths (and the
    # dev-output references they carry). Fil-C has no LTO linker plugin, so
    # garbage-collect sections at link time instead, as with GCC.
    (use (old: {
      env = old.env // {
        CFLAGS = "-fdata-sections -ffunction-sections -Wl,--gc-sections";
      };
    }))
    # Fil-C keeps each function's name and source file for its stack traces
    # outside the debug sections. Inlined OpenSSL header functions thus name
    # openssl-dev headers, which outputChecks forbids in $out.
    (tool pkgs.removeReferencesTo)
    (use (old: {
      postInstall =
        old.postInstall
        + "\n"
        + ''
          remove-references-to ${
            pkgs.lib.concatMapStringsSep " " (d: "-t ${pkgs.lib.getDev d}") (
              builtins.filter (d: d ? dev) old.buildInputs
            )
          } $out/lib/*.so*
        '';
    }))
  ])

  (for pkgs.liblc3 [
    # Meson's default b_lto would hand bitcode to the linker.
    (addMesonFlag "-Db_lto=false")
  ])

  (for pkgs.mpdecimal [
    # The x64 configuration multiplies with mulq inline assembly that Fil-C
    # rejects, so str(decimal.Decimal("1.5")) trapped in every Fil-C Python.
    (configure "MACHINE=ansi64")
  ])

  {
    gmp = for pkgs.gmp [
      # Upstream Fil-C disables this standalone assembly timing helper in
      # generated configure; the port extractor deliberately omits that file.
      (use (old: {
        postPatch = (old.postPatch or "") + ''
          substituteInPlace configure \
            --replace-fail 'SPEED_CYCLECOUNTER_OBJ_64=x86_64.lo' 'SPEED_CYCLECOUNTER_OBJ_64=' \
            --replace-fail 'cyclecounter_size_64=2' 'cyclecounter_size_64='
        '';
      }))
      (configure "--disable-assembly")
      (configure "--disable-fat")
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
    # 1.5.7's pointer-select inline asm is independent of ZSTD_DISABLE_ASM.
    (patch ./patches/zstd-pointer-select.patch)
    (skipCheck "too slow")
    (addCFlag "-DZSTD_DISABLE_ASM")
  ])

  (for pkgs.lzo [
    (skipTests "too slow")
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
    # Test adjustments for newer releases; the suite is skipped below.
    (skipPatch "t7703-ignore-ls-total.patch")
    (skipPatch "expect-gui--askyesno-failure-in-t1517.patch")
    (patch ./ports/patch/git-2.46.0.patch)
    (arg { withManual = true; })
    (arg { perlSupport = false; })
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
    (use rec {
      # our `pin` function doesn't work for this package, so we use a custom source.
      # i guess the version number of the package isn't verbatim in the url.
      version = "10.3p1";
      name = "openssh-${version}";
      src = pkgs.fetchurl {
        url = "mirror://openbsd/OpenSSH/portable/openssh-${version}.tar.gz";
        hash = "sha256-VmgqNruS3PS08Bb9jsjnQFm3mo3iXBXWcNcx59GORfQ=";
      };
    })
    (patch ./ports/patch/openssh-10.3p1.patch)
    (skipCheck "let's see")
    # preCheck preloads libredirect, whose dlsym(RTLD_NEXT, ...) interposition
    # cannot work under Fil-C; referencing it would still build it.
    (use { preCheck = ""; })
    (use {
      installCheckPhase = ''
        for binary in ssh sshd; do
          echo "verifying OpenSSH version $version"
          output=$($out/bin/$binary -V 2>&1)
          echo "got output: $output"
          echo "expected output: $(printf '^OpenSSH_%s,' "$version")"
          if ! echo "$output" | grep -P "$(printf '^OpenSSH_%s,' "$version")"; then
            echo "OpenSSH version verification failed"
            exit 1
          fi
        done
      '';
    })
    (arg { withFIDO = false; })
  ])

  (for pkgs.libssh2 [
    (skipCheck "network tests flaky")
    (configure "--disable-examples-build")
  ])

  (for pkgs.unbound [
    (configure "ac_cv_type_pthread_spinlock_t=no")
  ])

  # ━━━ Security ━━━

  (for pkgs.libseccomp [
    # seccomp_init probed the seccomp() syscall (317), which Fil-C refuses
    # by stopping the program, so every test died (rc=133). Report the
    # syscall as missing; filters still load through prctl(PR_SET_SECCOMP),
    # which Fil-C passes through, but without TSYNC or user notification.
    (patch ./patches/libseccomp-filc-no-seccomp-syscall.patch)
    # The regression suite only simulates filters; load one for real.
    (use (old: {
      postCheck = (old.postCheck or "") + ''
        $CC -Iinclude ${./tests/libseccomp-prctl-filter.c} \
          -Lsrc/.libs -Wl,-rpath,"$PWD/src/.libs" -lseccomp -o prctl-filter
        ./prctl-filter
      '';
    }))
  ])

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
    # --disable-asm leaves mpi/longlong.h's inline asm (for example
    # bsrq in _gcry_mpi_get_nbits, used by RSA), which Fil-C traps on.
    (addCFlag "-DNO_ASM")
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
    # The port is rooted above sourceRoot (src/); Nixpkgs' CVE patches are
    # -p1 relative to it and also apply to 1.21.3.
    (use (old: {
      prePatch = (old.prePatch or "") + ''
        patch -p2 < ${./ports/patch/krb5-1.21.3.patch}
      '';
    }))
  ])

  # pname is cyrus-sasl, so name the attribute explicitly.
  {
    cyrus_sasl = for pkgs.cyrus_sasl [
      # Upstream backport: configure never defined HAVE_TIME_H, so time()
      # and clock() were implicitly declared; Clang rejects that (GCC and
      # nixpkgs only warn), and the implicit int return truncates time_t.
      (patch ./patches/cyrus-sasl-time-h.patch)
    ];
  }

  (for pkgs.cryptsetup [
    (patch ./patches/cryptsetup-safe-alloc-mlock.patch)
  ])

  # mariadb-connector-c and libmysqlclient are aliases of the 3.3 series.
  {
    mariadb-connector-c_3_3 = for pkgs.mariadb-connector-c_3_3 [
      # Its export map is an implicit linker script with VERSION blocks and
      # unmangled symbol aliases; gold rejects it and only the driver's
      # --version-script handling knows Fil-C's symbol names.
      (patch ./patches/mariadb-connector-c-version-script.patch)
    ];
  }

  (for pkgs.p11-kit [
    (skipTests "1 failure")
  ])

  (for pkgs.libtirpc [
    # The source still uses K&R function definitions, which C23 removed.
    # Autoreconf'd configure asks for -std=gnu23 (GCC accepts them there
    # anyway; Clang does not), so keep Clang's gnu17 default.
    (configure "ac_cv_prog_cc_c23=no")
  ])

  (for pkgs.rpcbind [
    # Same K&R definitions as libtirpc (rpcinfo.c).
    (configure "ac_cv_prog_cc_c23=no")
  ])

  (for pkgs.duktape [
    (patch ./patches/duktape-valstack-rebase.patch)
    (use {
      doInstallCheck = true;
      installCheckPhase = ''
        "$out/bin/duk" ${./tests/duktape-valstack.js}
      '';
    })
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
    (patch ./ports/patch/cairo-1.18.0.patch)
  ])

  (for pkgs.pango [
    # 1.57 requires GLib 2.82; the GLib port is 2.80.4.
    (use {
      version = "1.56.3";
      src = pkgs.fetchurl {
        url = "mirror://gnome/sources/pango/1.56/pango-1.56.3.tar.xz";
        hash = "sha256-JgYlK8Jc2NJOG39+ksOicrN6zWc0NHtztHpIKDS6JJE=";
      };
    })
    (patch ./ports/patch/pango-1.54.0.patch)
  ])

  (for pkgs.gdk-pixbuf [
    (patch ./ports/patch/gdk-pixbuf-2.42.12.patch)
  ])

  (for pkgs.graphene [
    (patch ./ports/patch/graphene-1.10.8.patch)
    # gtk-doc generates an unported GType scanner; GIR generation stays on.
    (arg { withDocumentation = false; })
  ])

  (for pkgs.libepoxy [
    # Nixpkgs ties EGL to X11, but GTK's Wayland backend also needs EGL.
    (use (old: {
      mesonFlags =
        builtins.filter (f: !(pkgs.lib.hasPrefix "-Degl=" f)) old.mesonFlags
        ++ [
          "-Degl=yes"
        ];
      propagatedBuildInputs = pkgs.lib.unique (
        old.propagatedBuildInputs ++ [ final.libGL ]
      );
      env = old.env // {
        NIX_CFLAGS_COMPILE =
          (old.env.NIX_CFLAGS_COMPILE or "")
          + pkgs.lib.optionalString (
            (old.env.NIX_CFLAGS_COMPILE or "") == ""
          ) " -DLIBGL_PATH=\"${pkgs.lib.getLib final.libGL}/lib\"";
      };
    }))
  ])

  (for pkgs.fontconfig [
    # ports/patch/fontconfig-2.15.0.patch rebased onto Nixpkgs' 2.17.
    (patch ./patches/fontconfig-2.17-filc.patch)
    (use {
      postPatch = ''
        sed -i 's/ftglue.c/ftglue.c fcfilc.h fcfilc.c/' src/Makefile.am
      '';
    })
    (tool pkgs.autoreconfHook)
    (skipTests "tests pass but some test needs weird deps")
  ])

  (for pkgs.freetype [
    (patch ./ports/patch/freetype-2.13.3.patch)
    (skipPatch "subpixel-rendering.patch") # no need
    (skipPatch "enable-table-validation.patch") # no need
  ])

  (for pkgs.harfbuzz [
    (patch ./ports/patch/harfbuzz-9.0.0.patch)
    (arg {
      withGraphite2 = false;
    })
    (skipCheck "fuzzing fails")
  ])

  {
    # The upstream 3.4.4 port also applies to Nixpkgs' 3.6.5 release.
    libsoup_3 = for pkgs.libsoup_3 [
      (patch ./ports/patch/libsoup-3.4.4.patch)
    ];
  }

  {
    gtksourceview3 = for pkgs.gtksourceview3 [
      (patch ./patches/gtksourceview3-signal-types.patch)
      (tool pkgs.libxml2)
      (use (
        import ./toolchain/broadway-check.nix {
          inherit pkgs;
          gtk = final.gtk3;
        }
      ))
    ];
    gtksourceview4 = for pkgs.gtksourceview4 [
      (patch ./patches/gtksourceview4-signal-types.patch)
      (use (
        import ./toolchain/broadway-check.nix {
          inherit pkgs;
          gtk = final.gtk3;
        }
      ))
      (use { doCheck = true; })
    ];
  }

  # The 1.4 series needs the EOL libsoup 2.
  {
    gssdp_1_6 = for pkgs.gssdp_1_6 [
      (patch ./patches/gssdp-signal-types.patch)
    ];
    gupnp_1_6 = for pkgs.gupnp_1_6 [
      (patch ./patches/gupnp-gtype.patch)
    ];
  }

  (for pkgs.libhandy [
    (patch ./patches/libhandy-destroy-visible-child.patch)
    (use (old: {
      # librsvg is Rust; there is no Rust target for Fil-C. The icons are
      # pre-rendered below.
      checkInputs = builtins.filter (
        dep: !(pkgs.lib.hasInfix "librsvg" (dep.name or ""))
      ) (old.checkInputs or [ ]);
      postPatch = (old.postPatch or "") + ''
        # The target has no Rust SVG loader. Keep symbolic icon recoloring by
        # embedding GTK's encoded PNG format, generated with native tools.
        for icon in src/icons/scalable/*/*.svg; do
          directory=$(dirname "$icon" | sed s,scalable,128x128,)
          mkdir -p "$directory"
          GDK_PIXBUF_MODULE_FILE=${pkgs.librsvg}/${pkgs.gdk-pixbuf.binaryDir}/loaders.cache \
            ${pkgs.gtk3.dev}/bin/gtk-encode-symbolic-svg "$icon" 128x128 -o "$directory"
          png="$directory/$(basename "$icon" .svg).symbolic.png"
          test -s "$png"
          substituteInPlace src/handy.gresources.xml --replace-fail \
            "<file preprocess=\"xml-stripblanks\">''${icon#src/}</file>" \
            "<file>''${png#src/}</file>"
        done
      '';
    }))
    (use (
      import ./toolchain/broadway-check.nix {
        inherit pkgs;
        gtk = final.gtk3;
      }
    ))
  ])

  (for pkgs.glib [
    (pin "2.80.4" "sha256-JOApxd/JtE5Fc2l63zMHipgnxIk4VVAEs7kJb6TqA08=")
    (patch ./ports/patch/glib-2.80.4.patch)
    (patch ./patches/glib-gtype-api-ceiling.patch)
    (patch ./patches/glib-atomic-pointer-load.patch)
    (patch ./patches/glib-pointer-bit-wait.patch)
    (patch ./patches/glib-inline.patch)
    (skipPatch "split-dev-programs.patch")
    (patch ./patches/glib-split-backport.patch)
    (arg {
      libsysprof-capture = null;
      # Keep the bootstrap GLib free of scanner inputs as well as GIR output.
      withIntrospection = false;
      # gdbus-codegen runs on the build Python (3.13); the Fil-C set's
      # packaging is for the ported 3.12, leaving codegen's path empty.
      python3Packages = pkgs.python3Packages;
    })
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
    # gio-querymodules loads the modules it indexes, so consumers must run
    # this one rather than the build GLib's. Meson prefers a cross file's
    # binaries over its native pkg-config lookup.
    (use (old: {
      postFixup = (old.postFixup or "") + ''
        mkdir -p "$dev/share/meson"
        cat > "$dev/share/meson/gio-querymodules.ini" <<EOF
        [binaries]
        gio-querymodules = '$dev/bin/gio-querymodules'
        EOF
        cat >> "$dev/nix-support/setup-hook" <<EOF

        if (( hostOffset == 0 )) && [[ -z "\''${filcGioQuerymodulesCrossFile-}" ]]; then
          filcGioQuerymodulesCrossFile=1
          mesonFlagsArray+=("--cross-file=$dev/share/meson/gio-querymodules.ini")
        fi
        EOF
      '';
    }))
  ])

  {
    gobject-introspection-unwrapped = for pkgs.gobject-introspection-unwrapped [
      (pin "1.80.1" "sha256-od98Qk4VvaGrY5wA6QUbmt9c6hqeUS+KYDtTzRmbxtg=")
      (patch ./ports/patch/gobject-introspection-1.80.1.patch)
      (patch ./patches/gobject-introspection-filc-tools.patch)
      (patch ./patches/gobject-introspection-link-environment.patch)
      (skipPatch "Prefer-some-getters-over-others.patch")
      (arg {
        propagateFullGlib = false;
        # Fil-C executables run directly on the build machine. Bootstrap the
        # scanner here instead of recursively asking for a prebuilt scanner.
        gobject-introspection-unwrapped = null;
      })
      (removeMesonFlag "-Dgi_cross_use_prebuilt_gi=true")
      (addMesonFlag "-Dgi_cross_use_prebuilt_gi=false")
      (use (old: {
        nativeBuildInputs = builtins.filter (
          input: input != null
        ) old.nativeBuildInputs;
        # _giscanner is compiled with Fil-C and must be loaded by Fil-C Python.
        mesonFlags = old.mesonFlags ++ [
          "-Dpython=${
            final.python3.withPackages (ps: [
              ps.mako
              ps.markdown
              ps.setuptools
            ])
          }/bin/python3"
        ];
        outputs = builtins.filter (output: output != "devdoc") old.outputs;
        # The installed scanner also needs this when inspecting downstream
        # dumpers; a build-only PATH entry would leave those scans broken.
        postPatch = (old.postPatch or "") + ''
          substituteInPlace giscanner/shlibs.py \
            --replace-fail "['ldd', binary.args[0]]" "['${pkgs.glibc.bin}/bin/ldd', binary.args[0]]"
        '';
        # GLib's bootstrap build has no scanner. Install the GLib metadata
        # generated here, which GI 1.80 otherwise keeps only for its tests.
        # Also retain our patched test sources instead of Nixpkgs' native ones.
        postInstall = ''
          mkdir -p "$dev/share/gir-1.0" "$out/lib/girepository-1.0"
          for namespace in GLib GObject GModule Gio; do
            cp "gir/$namespace-2.0.gir" "$dev/share/gir-1.0/"
            cp "gir/$namespace-2.0.typelib" "$out/lib/girepository-1.0/"
          done
        '';
      }))
    ];
  }

  (for pkgs.wayland [
    (patch ./ports/patch/wayland-1.24.0.patch)
  ])

  (for pkgs.weston [
    # The test runner collected its tests from a linker section; register
    # them from constructors instead (upstream Fil-C's 12.0.5 patch).
    (patch ./ports/patch/weston-15.0.1.patch)
    # Nixpkgs' Neat VNC 1.0 update; the VNC backend is off.
    (skipPatch "8a1c91e771312d1e0d0cd92495ef717402784dae.patch")
    (arg { pipewireSupport = false; })
    (arg { rdpSupport = false; })
    (arg { remotingSupport = false; })
    (arg { vaapiSupport = false; })
    (arg { vncSupport = false; })
    (arg { xwaylandSupport = false; })
    (arg { lcmsSupport = false; })
    (addMesonFlag "-Dsystemd=false")
  ])

  (for pkgs.seatd [
    (arg { systemd = final.systemdLibs; })
  ])

  (for pkgs.alsa-lib [
    # ALSA's .symver module assembly is not part of the Fil-C ABI.
    (configure "--without-versioned")
    (patch ./patches/alsa-link-warning.patch)
    # snd_seq_ev_ext and snd_seq_ev_quote are packed, which puts their
    # pointers at misaligned offsets. Fil-C cannot keep a capability there
    # (a constant initializer used to crash the compiler, and the compiler
    # workaround was unsound), so drop `packed` under Fil-C. That grows
    # snd_seq_event_t from 28 to 32 bytes, so the ALSA sequencer (MIDI via
    # /dev/snd/seq) no longer matches the kernel; PCM audio is unaffected.
    (patch ./patches/alsa-seq-unpacked-pointers.patch)
  ])

  (for pkgs.spandsp [
    # Nixpkgs passes CC=${targetPrefix}cc, which is just "cc" for Fil-C, and
    # its depsBuildBuild puts the build GCC's cc first on PATH, so the
    # library came out native (and PipeWire's mSBC codec failed to link).
    (removeMakeFlag "CC=cc")
    (addMakeFlag "CC=${prev.stdenv.cc}/bin/cc")
  ])

  (for pkgs.pipewire [
    # Linker-section registration, pointer capabilities and test runtime
    # fixes; see docs/shared-library-unblocks.md.
    (patch ./patches/pipewire-log-topics.patch)
    (patch ./patches/pipewire-test-suites.patch)
    (patch ./patches/pipewire-pulse-modules.patch)
    (patch ./patches/pipewire-cpu-probe.patch)
    (patch ./patches/pipewire-pointer-arithmetic.patch)
    (patch ./patches/pipewire-pointer-properties.patch)
    (patch ./patches/pipewire-test-runtime.patch)
    (use (old: {
      # Valgrind's client requests are inline assembly on pointers, which
      # Fil-C rejects at run time; every pwtest suite died on them.
      env = (old.env or { }) // {
        NIX_CFLAGS_COMPILE = "-DNVALGRIND";
      };
      # The Fil-C cc-wrapper shares the build GCC's role infix
      # (x86_64_unknown_linux_gnu), so with a build compiler in
      # depsBuildBuild it also reads the *_FOR_BUILD flags. The native GLib
      # (for gdbus-codegen) then landed in RUNPATH ahead of the Fil-C GLib,
      # and the modules using GLib failed to dlopen. Only the build GCC's
      # compiler checks use these flags here.
      preConfigure = (old.preConfigure or "") + ''
        unset NIX_LDFLAGS_FOR_BUILD NIX_CFLAGS_COMPILE_FOR_BUILD
      '';
      preCheck = (old.preCheck or "") + ''
        export FUGC_THREADS="$NIX_BUILD_CORES"
        # Two independently loaded modules share the pointer-string table
        # (pipewire-pointer-properties.patch) under concurrent use.
        for module in a b; do
          $CC -shared -fPIC -I../spa/include \
            ${./tests/pipewire-pointer-module.c} -Lspa -lspa-filc-pointers \
            -Wl,-rpath,"$PWD/spa" -o "pointer-$module.so"
        done
        $CC -O2 ${./tests/pipewire-pointer-properties.c} -ldl -pthread \
          -o pointer-check
        timeout 30 ./pointer-check
        mesonCheckFlagsArray+=(--num-processes "$NIX_BUILD_CORES")
      '';
    }))
    # The GStreamer elements register GTypes through gsize once-inits.
    (removeMesonFlag "-Dgstreamer")
    (addMesonFlag "-Dgstreamer=disabled")
    (addMesonFlag "-Dgstreamer-device-provider=disabled")
    # PipeWire links libsystemd; it does not need the service manager's programs.
    (arg { systemd = final.systemdLibs; })
    # ROC's build takes ragel (and so colm and a target GCC) from the
    # host package set.
    (arg { rocSupport = false; })
    # ModemManager's libmbim, libqmi and libqrtr generate GType code that
    # assumes integer GTypes; PipeWire only uses it for HFP modem calls.
    (arg {
      modemmanager = final.modemmanager.overrideAttrs (old: {
        meta = old.meta // {
          badPlatforms = [ prev.stdenv.hostPlatform.system ];
        };
      });
    })
    # Nixpkgs enables the native HFP backend's ModemManager support
    # whenever BlueZ is available.
    (removeMesonFlag "-Dbluez5-backend-native-mm=enabled")
    (addMesonFlag "-Dbluez5-backend-native-mm=disabled")
  ])

  (for pkgs.libglvnd [
    (configure "--disable-asm")
  ])

  (for pkgs.libinput [
    (pin "1.29.1" "sha256-4BVHu9370s5hqugS/Lj/JEXwXXmmVRSMfjkvqpI9aq8=")
    (patch ./ports/patch/libinput-1.29.1.patch)
    # 1.29 predates the Lua plugin option Nixpkgs 26.05 sets.
    (arg { luaSupport = false; })
    (removeMesonFlag "-Dlua-plugins=disabled")
    (arg { libwacom = pkgs.hello; })
    (addMesonFlag "-Dlibwacom=false")
    (addMesonFlag "-Ddebug-gui=false")
  ])

  {
    libxkbcommon = (
      for pkgs.libxkbcommon [
        (patch ./ports/patch/libxkbcommon-xkbcommon-1.11.0.patch)
        (skipTests "eh")
        (addMesonFlag "-Denable-x11=false")
      ]
    );
  }

  (for pkgs.libtiff [
    (patch ./ports/patch/tiff-4.6.0.patch)
    (arg { libdeflate = final.hello; })
  ])

  (for pkgs.libwebp [
    (patch ./ports/patch/libwebp-1.4.0.patch)
    (patch ./patches/libwebp-xgetbv.patch)
  ])

  (for pkgs.libevdev [
    (pin "1.11.0" "sha256-Y/TqFImFihCQgOC0C9Q+TgkDoeEuqIjVgduMSVdHwtA=")
    (patch ./ports/patch/libevdev-1.11.0.patch)
  ])

  (for pkgs.valgrind [ (broken "not yet ported") ])

  (for pkgs.cups [
    (arg { gnutls = final.openssl; })
  ])

  {
    # Its pname is ghostscript-with-X, so name the attribute explicitly.
    ghostscript = for pkgs.ghostscript [
      (patch ./patches/ghostscript-filc.patch)
    ];
  }

  (for pkgs.dbus [
    (arg { systemdMinimal = final.systemdLibs; })
    (arg { libapparmor = final.hello; })
    # dbus 1.16 builds with Meson.
    (removeMesonFlag "-Dapparmor")
    (addMesonFlag "-Dapparmor=disabled")
  ])

  # ━━━ Development Tools & Libraries ━━━

  (for pkgs.fmt [
    # Works around Fil-C's clang passing small records that contain unions
    # as integers, which dropped the pointers in one-argument
    # make_format_args stores (wide and custom-type formatting).
    (patch ./patches/fmt-arg-store-in-memory.patch)
    (use {
      # float_test.isnan: the Fil-C runtime leaves FE_INEXACT set at start.
      # util_test.format_system_error: allocating SIZE_MAX / 2 bytes is a
      # Fil-C safety panic, not std::bad_alloc. See docs/filc-findings.md.
      preCheck = ''
        export GTEST_FILTER=-float_test.isnan:util_test.format_system_error
      '';
    })
  ])

  (for pkgs.doctest [
    (addCFlag "-Wno-reserved-macro-identifier")
    (addCFlag "-Wl,-lm")
    # The self-tests install signal handlers on an alternate stack
    # (sigaltstack) and break into the debugger with llvm.debugtrap; Fil-C
    # supports neither. The library is header-only.
    (skipCheck "sigaltstack and debugtrap")
  ])

  # Named explicitly: the pname is "catch2", which is Catch2 v2's attribute.
  {
    catch2_3 = for pkgs.catch2_3 [
      # Catch2's fatal-signal handler runs on an alternate stack
      # (sigaltstack), which Fil-C does not support; every test run aborted
      # in FatalConditionHandler::engage_platform. Fil-C also refuses
      # handlers for SIGSEGV and the like, so the handler could not work
      # anyway. The option is written to catch_user_config.hpp, so test
      # suites that link this Catch2 skip the handler too.
      (addCMakeFlag "-DCATCH_CONFIG_NO_POSIX_SIGNALS=ON")
    ];
  }

  # Their suites use doctest, whose signal handling needs sigaltstack.
  (for pkgs.nlohmann_json [
    (addCMakeFlag "-DCMAKE_CXX_FLAGS=-DDOCTEST_CONFIG_NO_POSIX_SIGNALS")
  ])
  (for pkgs.toml11 [
    (addCMakeFlag "-DCMAKE_CXX_FLAGS=-DDOCTEST_CONFIG_NO_POSIX_SIGNALS")
  ])

  (for pkgs.gettext [
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
    # 0.194's configure requires pkg-config; Nixpkgs adds it only for debuginfod.
    (tool pkgs.pkg-config)
    (skipTests "some tests fail")
  ])

  (for pkgs.libcbor [
    (patch ./patches/libcbor-test-math.patch)
    # Fil-C emits instrumented objects; the final native linker cannot consume
    # the LLVM bitcode produced by libcbor's automatic IPO selection.
    (addCMakeFlag "-DCMAKE_INTERPROCEDURAL_OPTIMIZATION=OFF")
    (addCMakeFlag "-DWITH_EXAMPLES=OFF")
    (addCMakeFlag "-DSANITIZE=OFF")
    (use { doCheck = true; })
  ])

  (for pkgs.libapparmor [
    # Configure runs the target Python config tool when linking its extension.
    # Since 4.1 it also imports setuptools with that interpreter.
    (configure "PYTHON=${
      final.python3.withPackages (ps: [ ps.setuptools ])
    }/bin/python3")
    (configure "PYTHON_CONFIG=${final.python3}/bin/python3-config")
  ])

  {
    libcap_ng = for pkgs.libcap_ng [
      (use (old: {
        # capng_change_id applies ambient capabilities, but the Fil-C runtime
        # rejects prctl(PR_CAP_AMBIENT) with ENOSYS, so it returns -9.
        postPatch = (old.postPatch or "") + ''
          substituteInPlace src/test/Makefile.am \
            --replace-fail "thread_test change_id_test" "thread_test"
        '';
      }))
    ];
    pam = for pkgs.linux-pam [ (skipCheck "test setup issues") ];
  }

  (for pkgs.cmocka [
    (skipTests "some tests fail")
    (addCMakeFlag "-DWITH_EXAMPLES=OFF")
  ])

  (for pkgs.libbsd [
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
    (skipTests "some tests fail")
  ])

  (for (pkgs.callPackage ./packages/libmicrohttpd.nix { }) [ ])

  # ━━━ Languages ━━━

  {
    # nixpkgs only packages Perl 5.42; the Fil-C port targets 5.40.0.
    perl5 = (
      for pkgs.perl5 [
        (arg {
          version = "5.40.0";
          sha256 = "sha256-x0A0jzVzljJ6l5XT6DI7r9D+ilx4NfwcuroMyN/nFh8=";
          # Nixpkgs builds perl.pkgs with its own perl5 attribute; use the port.
          self = final.perl5;
          # buildPerlPackage puts perl in nativeBuildInputs, which Nixpkgs
          # 26.05 resolves to the package set's build-host splice. That was
          # the build platform's perl, which configured XS modules with its
          # own Config and then loaded the Fil-C objects in their tests. Fil-C
          # programs run on the build machine, so splice the port there.
          # Module fixes from ports/perl-modules.nix apply to the scope, so
          # dependents and withPackages see them.
          passthruFun =
            args:
            let
              upstream =
                (import "${prev.path}/pkgs/development/interpreters/perl" {
                  # Recover Nixpkgs' passthruFun, which calls callPackage itself.
                  callPackage = f: a: a.passthruFun or (final.callPackage f a);
                }).perl5
                  (args // { perlOnBuildForHost = args.self; });
              pkgs = upstream.pkgs.overrideScope (import ./ports/perl-modules.nix);
            in
            upstream
            // {
              inherit pkgs;
              withPackages = f: upstream.buildEnv.override { extraLibs = f pkgs; };
            };
        })
        (patch ./ports/patch/perl-5.40.0.patch)
        (patch ./patches/perl-5.40-only-c-locale.patch)
        (patch ./patches/perl-5.40-encode-shared-ptrtable.patch)
        (patch ./patches/perl-5.40-b-overlay-key.patch)
        (patch ./patches/perl-5.40-digest-sha-ptrtable.patch)
        (use (old: {
          # postPatch replaces the bundled Compress-Raw-Zlib with a newer
          # release, discarding the port's typemap change.
          postPatch = old.postPatch + ''
            substituteInPlace cpan/Compress-Raw-Zlib/typemap \
              --replace-fail '$var = INT2PTR($type, tmp);' \
                '$var = zptrtable_decode(Perl_xsub_ptrtable, tmp);'
          '';
        }))
        (skipCheck "too slow")
        # NO overrides arg - that breaks withPackages!
      ]
    );
  }

  {
    python312 = for pkgs.python312 [
      (pin "3.12.5" "sha256-+oouEsXmILCfU+ZbzYdVDS5aHi4Ev4upkdzFUROHY5c=")
      (patch ./ports/patch/Python-3.12.5.patch)
      (patch ./patches/python-filc-triplet-detection.patch)
      (patch ./patches/python-faulthandler.patch)
      # nixpkgs' separate debug info adds -Wa,--compress-debug-sections, which
      # Fil-C's assembler rejects, and busybox skips the preConfigure hook
      # removeCFlag relies on.
      (use { separateDebugInfo = false; })
      (arg { enableLTO = false; })
      (configure "--without-pymalloc")
      (configure "--without-freelists")
      (configure "ac_cv_func_chflags=no")
      (configure "ac_cv_func_lchflags=no")
      (configure "ac_cv_func_sigaltstack=no")
      (configure "ac_cv_gcc_asm_for_x64=no")
      (configure "ac_cv_gcc_asm_for_x87=no")
      (configure "ac_cv_gcc_asm_for_mc68881=no")
      # Nixpkgs assumes x87 double rounding when cross compiling. With no x87
      # inline assembly to fix the precision, that disables short float repr
      # (repr(12.3) == '12.300000000000001'). Fil-C uses SSE2 arithmetic.
      (removeConfigureFlag "ac_cv_x87_double_rounding=yes")
      (configure "ac_cv_x87_double_rounding=no")
      (arg {
        packageOverrides = import ./ports/pythonPorts-as-overlay.nix pkgs;
      })
    ];
  }

  {
    ruby_3_3 = (
      for ./ports/ruby.nix [
        (patch ./ports/patch/ruby-3.3.10.patch)
        # Upstream's Fil-C port uses pthread coroutines, not native assembly.
        (configure "--with-coroutine=pthread")
        # Autoconf 2.73 would record CC as "clang -std=gnu23" in rbconfig,
        # which native gem extensions then inherit; keep the compiler default.
        (configure "ac_cv_prog_cc_c23=no")
        # Disable ractor shareability deep checking - requires rb_objspace_reachable_objects_from
        # which isn't implemented in Fil-C. Return false = conservatively assume not shareable.
        (astRewrite "ractor.c" "c"
          "bool rb_ractor_shareable_p_continue($PARAM) { $$$BODY }"
          "bool rb_ractor_shareable_p_continue($PARAM) {
#ifdef __FILC__
    return false;
#else
    $$$BODY
#endif
}"
        )
        # Also patch rb_ractor_make_shareable to skip traversal
        (astRewrite "ractor.c" "c"
          "VALUE rb_ractor_make_shareable(VALUE $OBJ) { $$$BODY }"
          "VALUE rb_ractor_make_shareable(VALUE $OBJ) {
#ifdef __FILC__
    FL_SET_RAW($OBJ, RUBY_FL_SHAREABLE);
    return $OBJ;
#else
    $$$BODY
#endif
}"
        )

      ]
    );
  }

  # ━━━ Terminal & System ━━━

  (for pkgs.libcap [
    (pin "2.70" "sha256-I6bviq2vHj6HX2M7stEWz++JUtunvHxWmxNFjhlSsw8=")
    (arg { withGo = false; })
    (arg { usePam = false; })
  ])

  {
    binutils-unwrapped = for pkgs.binutils-unwrapped [
      (src "2.43.1" "sha256-vsqsXSleA3WHtjpC+tV/49nXuD9HjrJLZ/nuxdDxhy8=" (
        version: "mirror://gnu/binutils/binutils-${version}.tar.bz2"
      ))
      (patch ./ports/patch/binutils-2.43.1.patch)
    ];
  }

  (for pkgs.kbd [
    # ports/patch/kbd-2.6.4.patch rebased onto Nixpkgs' 2.9.
    (patch ./patches/kbd-2.9-filc.patch)
  ])

  (
    let
      getent = pkgs.writeShellScriptBin "getent" ''
        ${final.stdenv.cc.libc}/bin/getent "$@"
      '';
    in
    {
      # systemdMinimal and systemdLibs derive from this port through .override;
      # applying the patch here gives all three variants the same ABI fixes.
      systemd = for pkgs.systemd [
        (pin "256.4" "sha256-eGHVRBkPk4ysGyQmJNeMlv4uu8e3L4YWboi1BFHG+lg=")
        (patch ./ports/patch/systemd-256.4.patch)
        (arg { withKexectools = false; })
        (arg { withLibseccomp = false; })
        # EFI/BPF/kexec emit kernel or firmware code, outside Fil-C userspace.
        (arg {
          withLibBPF = false;
          withEfi = false;
          withBootloader = false;
        })
        (link getent)
        (link final.libcap) # dropped from the recipe once systemd stopped needing it
        (use (
          old:
          {
            # Nixpkgs stopped rewriting this path for systemd 258+.
            postPatch = old.postPatch + ''
              substituteInPlace src/nspawn/nspawn-setuid.c \
                --replace-fail /usr/bin/getent ${getent}/bin/getent
            '';
          }
          // pkgs.lib.optionalAttrs (old.pname != "systemd-minimal-libs") {
            # This getent wrapper intentionally calls the target libc at runtime.
            # Keep rejecting every other accidental native build-tool reference.
            disallowedReferences = builtins.filter (p: p != getent) (
              old.disallowedReferences or [ ]
            );
          }
        ))

        # Nixpkgs' patches target 260; use the 25.05 copies for 256.
        (skipPatch "Change-usr-share-zoneinfo-to-etc-zoneinfo.patch")
        (skipPatch "path-util.h-add-placeholder-for-DEFAULT_PATH_NORMAL.patch")
        (patch ./patches/systemd-256-etc-zoneinfo.patch)
        (patch ./patches/systemd-256-default-path-placeholder.patch)
        (patch ./patches/systemd-256-no-statedir.patch)
        (patch ./patches/systemd-256-no-ssh-dropins.patch)
        # not in this version
        (removeMesonFlag "-Dshellprofiledir")
        (removeMesonFlag "-Dswapon-path")
        (removeMesonFlag "-Dswapoff-path")
        (removeMesonFlag "-Dsysupdated")
        (removeMesonFlag "-Dnspawn")
        # Options that 260 removed, set as Nixpkgs 25.05 did for 256/257.
        (addMesonFlag "-Dlibidn=disabled")
        (addMesonFlag "-Dlibiptc=disabled")
        (addMesonFlag "-Dsysvinit-path=")
        (addMesonFlag "-Dsysvrcnd-path=")
        (addMesonFlag "-Dsshconfdir=no")
        (use {
          # the automatic patchelf hook was segfaulting
          # while trying to patch some debug info files?!
          separateDebugInfo = false;
          # Nixpkgs 26.05 bans bash from the closure; libapparmor's Python
          # bindings bring the Fil-C interpreter (and its bash) along.
          disallowedRequisites = [ ];
        })

        # this seems to not be a real problem
        (use { autoPatchelfIgnoreMissingDeps = [ "*" ]; })
      ];
    }
  )

  (for pkgs.go [
    (broken "not yet ported")
  ])

  (for pkgs.ttyd [
    (skipCheck "network service tests")
  ])

  (for pkgs.procps [
    (patch ./ports/patch/procps-ng-4.0.4.patch)
  ])

  {
    util-linux = for pkgs.util-linuxMinimal [
      parallelize
    ];
  }

  (for pkgs.e2fsprogs [
    (arg { withFuse = false; })
    (skipTests "requires special setup")
  ])

  (for pkgs.sqlite [
    (arg { interactive = true; })
    (skipCheck "too slow")
    (removeCFlag "-DSQLITE_ENABLE_STMT_SCANSTATUS")
  ])

  (for pkgs.jq [
    # The suite dumps deeply nested values recursively; Fil-C frames are
    # larger than native ones and overflow the default 8 MiB stack.
    (use (old: {
      preInstallCheck = (old.preInstallCheck or "") + ''
        ulimit -s 65536
      '';
    }))
  ])

  # callPackage splices python3Packages by name, and the build platform's is
  # 3.13, so setuptools came from 3.13 while the build ran the ported 3.12.
  # The 3.12 set splices against its own build-platform 3.12.
  (for pkgs.nixos-rebuild-ng [
    (arg { python3Packages = final.python312.pkgs; })
    # A test uses Generator's one-argument form, which needs Python 3.13.
    (use (old: {
      postPatch =
        (old.postPatch or "")
        + "\n"
        + ''
          substituteInPlace tests/test_tmpdir.py \
            --replace-fail 'typing.Generator[None]' 'typing.Generator[None, None, None]'
        '';
    }))
  ])

  # Fil-C's libc has no vfork. At shutdown PID 1 vforks a child to reboot and
  # stays suspended until the child is gone; fork and wait for it instead.
  (for pkgs.finit [
    (use (old: {
      postPatch =
        (old.postPatch or "")
        + "\n"
        + ''
          substituteInPlace src/sig.c --replace-fail 'if (vfork()) {' \
            'if (({ pid_t p = fork(); if (p > 0) waitpid(p, NULL, 0); p; })) {'
        '';
    }))
  ])

  (for pkgs.strace [
    (use { postPatch = "sed -i 's/ vfork/ fork/g' */strace.c"; })
    # libunwind's register-level unwinder is hand-written assembly without
    # SaRCAsm annotations. strace uses elfutils for -k instead.
    (arg { libunwind = null; })
  ])

  (for pkgs.runit [
    (patch ./patches/runit-pid-namespace.patch)
  ])

  # ━━━ Web & Network Services ━━━

  (for pkgs.redis [
    # Aligned encoded reply buffers; no madvise on the heap after fork.
    (patch ./patches/redis-filc.patch)
    (use (old: {
      makeFlags = old.makeFlags ++ [
        # Redis's default -O3 turns on LTO, which Fil-C does not have.
        "OPTIMIZATION=-O2"
        # The test modules' Makefile hard-codes gcc.
        "CC=cc"
        "LD=cc"
      ];
      # The tests call pgrep; Nixpkgs' `ps` here is procps' ps alone.
      nativeCheckInputs = old.nativeCheckInputs ++ [ pkgs.procps ];
      checkPhase =
        let
          skips = [
            # The jemalloc shim ignores malloc_conf, and has no per-size
            # accounting or active defragmentation, so fragmentation always
            # reads 1.00.
            "--tags -defrag"
            ''--skiptest "je_malloc_conf compile-time tuning is active"''
            ''--skiptest "Reduce defrag CPU usage when module data can't be defragged"''
            # Fil-C gives the program copies of argv, so rewriting them does
            # not change /proc/<pid>/cmdline.
            ''--skiptest "Process title set as expected"''
            # Crash reports need SIGSEGV handlers, which Fil-C refuses.
            "--skipunit unit/moduleapi/crash"
            # The key metadata API passes pointers as uint64_t, which drops
            # their capability; the test modules store strings that way.
            "--skipunit unit/moduleapi/keymeta"
            "--skipunit unit/moduleapi/ksn_notify_side_effect"
            # They load payloads that request exabyte allocations and expect
            # zmalloc to fail; Fil-C stops the program instead.
            ''--skiptest "corrupt payload: fuzzer findings - OOM in dictExpand"''
            ''--skiptest "corrupt payload: fuzzer findings - huge string"''
            # Crash reports with stack traces: SIGSEGV handlers again, and
            # the port builds without backtrace support.
            "--skipunit integration/logging"
          ];
          last = ''--skiptest "Check MEMORY USAGE for embedded key strings with jemalloc"'';
        in
        assert pkgs.lib.hasInfix last old.checkPhase;
        builtins.replaceStrings
          [
            "./runtest \\\n"
            last
          ]
          [
            "set -o pipefail\n./runtest \\\n"
            (
              pkgs.lib.concatMapStrings (s: s + " \\\n  ") skips
              # The test runner redraws lines with carriage returns and
              # colours them, which leaves the Nix log blank.
              + last
              + " 2>&1 | sed -u -e 's/\\r/\\n/g' -e 's/\\x1b\\[[0-9;]*m//g'"
            )
          ]
          old.checkPhase;
      postPatch = (old.postPatch or "") + ''
        # Nixpkgs' system-jemalloc patch still builds deps/jemalloc, whose
        # configure fails; Redis links the jemalloc shim instead.
        sed -i 's/^\tDEPENDENCY_TARGETS+= jemalloc$//' src/Makefile
        ! grep -q 'DEPENDENCY_TARGETS+= jemalloc' src/Makefile
      '';
    }))
  ])

  (for pkgs.lighttpd [
    (patch ./patches/lighttpd-filc.patch)
    (arg { enableMagnet = true; })
    (arg { enableWebDAV = true; })
    (arg { enablePam = true; })
    (arg { lua5_1 = pkgs.lua5; })
    (skipCheck "test suite issues")
  ])

  (for pkgs.tor [
    (arg {
      systemd = final.systemdLibs;
      libseccomp = null;
      # libcap = null;
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

  {
    tinycc = for pkgs.tinycc [
      (patch ./patches/tinycc-alignment.patch)
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
    ];
  }

  (for pkgs.quickjs [
    # Nixpkgs' 2026-06-04 release rather than upstream Fil-C's 2024-02-14
    # snapshot: the old one crashed on greedy regexps under Fil-C and is far
    # too slow for yt-dlp's challenge solver (it asks for >= 2025-04-26).
    (patch ./patches/quickjs-2026-filc.patch)
    # Fil-C frames are larger; the native 1 MiB JS stack limit overflows on
    # yt-dlp's solver, which runs qjs without --stack-size.
    (addCFlag "-DJS_DEFAULT_STACK_SIZE=4194304")
    (use (old: {
      # The install check reuses $out for a temporary file.
      postInstallCheck = (old.postInstallCheck or "") + ''
        ${builtins.placeholder "out"}/bin/qjs ${./tests/quickjs-regexp.js}
      '';
    }))
  ])

  (for pkgs.trealla [
    (arg { lineEditingLibrary = "readline"; })
    (use {
      version = "unstable-2026-09-05";
      # GitHub's archive bytes for this commit changed; hash the contents.
      src = pkgs.fetchFromGitHub {
        owner = "trealla-prolog";
        repo = "trealla";
        rev = "12f4cbd7fc2269265e7306775ded2f6410671499";
        hash = "sha256-PL5RyiakGDyFLnoSiOS5/b2AoRNwqoG7W+ShYsNl5a4=";
      };
    })
    (use (old: {
      postPatch =
        builtins.replaceStrings [ "Makefile" ] [ "GNUmakefile" ]
          old.postPatch;
      makeFlags = old.makeFlags ++ [
        "READLINE=1"
        "LIBDIR=$(out)/share/trealla"
      ];
      postInstall = (old.postInstall or "") + ''
        mkdir -p $out/share/trealla/library
        find library -name '*.pl' -exec cp --parents -t $out/share/trealla {} +
      '';
    }))
    (patch ./patches/trealla-filc-ffi-zptrtable.patch)
    (patch ./patches/trealla-filc-tabling-cursors.patch)
    (skipTests "runtime coverage lives in checks.x86_64-linux.trealla")
  ])

  (for pkgs.wasm3 [
    markAsNotNecessarilyInsecure
  ])

  {
    kittydoom = for ./packages/kitty-doom.nix [ ];
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
        dbus = null;
        withX = false;
        withGTK3 = false;
        withXwidgets = false;
        withMailutils = false;
        withNS = false;
        withPgtk = false;
        withImageMagick = false;
        withGpm = false;
        withSystemd = true;
        withNativeCompilation = false;
        withCsrc = true;
        withCairo = false;
        withAthena = false;
        withMotif = false;
        withDbus = false;
        withAlsaLib = false;
        withGlibNetworking = false;
        withXinput2 = false;
        withJansson = true;
        # The fork below is a git tree without a generated configure.
        srcRepo = true;
      })
      (pin "30.1" "sha256-eTWjpRgLXbA9OQZnbrWPIHPcbj/QYkv58I3IWx5lCIQ=")
      (link final.zlib)
      (use {
        src = pkgs.fetchFromGitHub {
          owner = "mbrock";
          repo = "emacs";
          rev = "a55126f6150b43ffc2fbc0682dcd594d5a98f96d";
          hash = "sha256-LWnniS61uEE55tfMV8HTQdKzs+IPwr5dwoSxyfApTss=";
        };
      })
      # Nixpkgs' patches target 30.2; the fork is based on 30.1.
      (skipPatch "02_all_ts-query-pred.patch")
      (patch ./patches/emacs-fork-ts-query-pred.patch)
      (skipPatch "CVE-2026-79992.patch")
      (patch ./patches/emacs-fork-CVE-2026-79992.patch)
      (configure "--with-gnutls=ifavailable")
      (configure "--with-dumping=none")
      (configure "--with-pdumper=no")
      (configure "--with-unexec=no")
      (configure "--with-native-compilation=yes")
      (configure "--with-native-compilation-backend=comphack")
      (configure "--with-comphack-cc=${final.gnufilc0}/bin/clang")
      (addMakeFlag "NATIVE_COMP_ZYGOTE=yes")
      (addMakeFlag "NATIVE_COMP_ZYGOTE_JOBS=12")
      (use (old: {
        preBuild = (old.preBuild or "") + ''
          # Fil-C's larger native frames overflow the usual 8 MiB stack while
          # Comphack compiles large preloaded files such as window.el.
          ulimit -S -s 65536
        '';
        postInstall = (old.postInstall or "") + ''
          # A no-dump Emacs runs loadup.el at startup before startup.el can
          # process EMACSNATIVELOADPATH.  Make the installed ELNs visible at
          # the early path derived from the executable prefix.
          ln -s "lib/emacs/${old.version}/native-lisp" "$out/native-lisp"
        '';
        # Fil-C sizes the main thread's stack from RLIMIT_STACK at startup.
        # Byte-compiling large packages such as eat overflows 8 MiB too, so
        # raise the soft limit in every build that uses this Emacs.
        setupHook = pkgs.writeText "emacs-setup-hook.sh" (
          builtins.readFile old.setupHook
          + ''

            if [[ $(ulimit -S -s) != unlimited && $(ulimit -S -s) -lt 65536 ]]; then
              ulimit -S -s 65536 2>/dev/null || true
            fi
          ''
        );
      }))
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

  (for pkgs.gnutls [
    # Upstream's 3.8.7.1 fix also applies to Nixpkgs' 3.8.9 release.
    (patch ./ports/patch/gnutls-3.8.7.1.patch)
    (configure "--disable-hardware-acceleration")
  ])

  (for pkgs.at-spi2-core [
    (src "2.60.5" "sha256-YFmnfVB0OP9sjW0GAl+Pn1d0+g+Oq+nJsFmxzEHhu8A=" (
      v:
      "https://download.gnome.org/sources/at-spi2-core/2.60/at-spi2-core-${v}.tar.xz"
    ))
    (patch ./ports/patch/at-spi2-core-2.60.5.patch)
    (tool pkgs.python3)
    (addMesonFlag "-Dintrospection=enabled")
  ])

  (for pkgs.dbus-glib [
    (patch ./patches/dbus-glib-gtype.patch)
  ])

  (for pkgs.json-glib [
    (patch ./patches/json-glib-gtype.patch)
  ])

  {
    glibmm = for pkgs.glibmm [ (patch ./patches/glibmm-gtype.patch) ];
    # glibmm 2.88 needs GLib 2.87; 2.80 is the newest series that accepts
    # the Fil-C GLib 2.80.
    glibmm_2_68 = for pkgs.glibmm_2_68 [
      (src "2.80.1" "sha256-8aDA7FFON3S/mTOW8X9yEGtAkSx9fMnRDaMboVUX4/U=" (
        v: "mirror://gnome/sources/glibmm/2.80/glibmm-${v}.tar.xz"
      ))
      (patch ./patches/glibmm-gtype.patch)
    ];
    # Match the Fil-C GTK 4.14; gtkmm 4.22 needs GTK 4.22.
    gtkmm4 = for pkgs.gtkmm4 [
      (src "4.14.0" "sha256-k1CgREt0TKPcaVhuvRtnB1IJIrbZ9PIyEDzmA6Jx7No=" (
        v: "mirror://gnome/sources/gtkmm/4.14/gtkmm-${v}.tar.xz"
      ))
      (use {
        # Fil-C GTK has no X11 backend; run the tests on Broadway instead
        # of Xvfb.
        nativeCheckInputs = [ ];
        checkPhase = ''
          runHook preCheck
          export XDG_RUNTIME_DIR="$TMPDIR/runtime"
          mkdir -m 700 "$XDG_RUNTIME_DIR"
          export GDK_BACKEND=broadway BROADWAY_DISPLAY=:5 GTK_A11Y=none
          ${final.gtk4.out}/bin/gtk4-broadwayd :5 &
          broadway_pid=$!
          for _ in $(seq 100); do
            [ -S "$XDG_RUNTIME_DIR/broadway6.socket" ] && break
            sleep 0.1
          done
          meson test --print-errorlogs
          kill "$broadway_pid"
          runHook postCheck
        '';
      })
    ];
  }

  {
    # Its pname is libdbusmenu-glib.
    libdbusmenu = for pkgs.libdbusmenu [
      (patch ./patches/libdbusmenu-gtype.patch)
    ];
  }

  (for pkgs.dconf [
    (patch ./patches/dconf-filc-gtype.patch)
    # Vala is used only to generate API metadata here, not linked into dconf.
    (arg {
      vala = pkgs.vala;
      withDocs = false;
    })
    (use (old: {
      postPatch = (old.postPatch or "") + ''
        # Keep the ABI checks, comparing against Fil-C's exported names.
        sed -i 's/^/pizlonated_/' client/symbols.txt gsettings/symbols.txt
      '';
    }))
  ])

  {
    # Named explicitly: the pname is "gtk+". GTK 2 has no upstream Fil-C port;
    # this applies the GTK 3 port's pointer-GType changes to 2.24.33 (see
    # docs/gtk-ports.md).
    gtk2 = for pkgs.gtk2 [
      (patch ./patches/gtk2-filc-gtype.patch)
    ];

    gtk3 = for pkgs.gtk3 [
      (pin "3.24.52" "sha256-gJMfpHKne5oWT2dA48C0RPrGdwBUYy01p/+dZ55ee58=")
      (patch ./ports/patch/gtk-3.24.52.patch)
      # GTK3 does not request GLib among its generator inputs itself.
      (tool final.buildPackages.glib)
      (removeMesonFlag "-Dgtk_doc=true")
      (addMesonFlag "-Dgtk_doc=false")
      (use (old: {
        outputs = builtins.filter (output: output != "devdoc") old.outputs;
      }))
      (arg {
        x11Support = false;
        xineramaSupport = false;
        waylandSupport = true;
        broadwaySupport = true;
      })
    ];

    gtk4 = for pkgs.gtk4 [
      (pin "4.14.5" "sha256-VUfyufAGsTOZPgcLh8F4BOBR79o5E/6soRCPor5B4k0=")
      # Nixpkgs' 32-bit Vulkan fix targets newer releases; Vulkan is off here.
      (skipPatch "fix-32bit-VkImage-null.patch")
      (patch ./ports/patch/gtk-4.14.5.patch)
      (patch ./patches/gtk4-broadway-node-alignment.patch)
      (link final.libdrm)
      (addMesonFlag "-Dintrospection=enabled")
      # Keep the UI toolkit independent of the optional GStreamer video
      # backend and its complete codec/plugin dependency tree.
      (addMesonFlag "-Dmedia-gstreamer=disabled")
      (use (old: {
        buildInputs = builtins.filter (
          input:
          !(builtins.elem (input.pname or "") [
            "gst-plugins-base"
            "gst-plugins-bad"
          ])
        ) old.buildInputs;
      }))
      (arg {
        x11Support = false;
        xineramaSupport = false;
        waylandSupport = true;
        broadwaySupport = true;
        vulkanSupport = false;
        trackerSupport = false;
      })
    ];
  }

  (for pkgs.rustc [
    (broken "oh sweet summer child")
  ])
]
