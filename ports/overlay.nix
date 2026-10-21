# Overlay for Fil-C ported packages
# Converts the port list from ../ports.nix into a nixpkgs overlay

pkgs: final: prev:
let
  portDSL = import ./default.nix { inherit (pkgs) lib pkgs; };
  portList = import ../ports.nix { inherit pkgs prev final; };

  # Fil-C overrides for a Nix component scope, shared by upstream Nix and
  # Determinate Nix. Boehm GC scans the native stack and data segments, which
  # Fil-C objects do not live in; Fil-C collects garbage itself. seccomp
  # filters and the static busybox sandbox shell are unavailable too.
  nixFilcOverrides = nfinal: nprev: {
    # Fil-C has no LTO; Nix enables it for its release builds.
    mesonComponentOverrides =
      finalAttrs: prevAttrs:
      let
        base = nprev.mesonComponentOverrides finalAttrs prevAttrs;
      in
      base
      // {
        preConfigure = (base.preConfigure or prevAttrs.preConfigure or "") + ''
          appendToVar mesonFlags "-Db_lto=false"
        '';
      };
    # Fil-C has no sigaltstack, and it catches stack overflow itself.
    nix-main = nprev.nix-main.overrideAttrs (old: {
      postPatch =
        (old.postPatch or "")
        + "\n"
        + ''
          substituteInPlace $(find . -path '*/unix/stack.cc') --replace-fail \
            '#if defined(SA_SIGINFO) && defined(SA_ONSTACK)' \
            '#if defined(SA_SIGINFO) && defined(SA_ONSTACK) && !defined(__FILC__)'
        '';
    });
    nix-functional-tests = nprev.nix-functional-tests.overrideAttrs (old: {
      # The suite runs whichever `nix` is on PATH. Nixpkgs asks for
      # nix-cli.__spliced.hostHost, which this scope lacks, so it fell
      # back to the build platform's (glibc) Nix: every functional test
      # exercised native Nix, and the Fil-C test plugin could not load
      # into it (undefined pizlonated_* symbols). Fil-C programs run on
      # the build machine, so test the Fil-C Nix.
      nativeBuildInputs = map (
        p: if (p.pname or "") == "nix" then nfinal.nix-cli else p
      ) old.nativeBuildInputs;
      postPatch =
        (old.postPatch or "")
        + "\n"
        + ''
          pushd "$(dirname "$(find -L . -path '*/common/vars.sh' -print -quit)")/.." >/dev/null
          # The harness enables sandbox tests when `unshare --user` works,
          # but this Nix cannot sandbox (no clone; see nix-util below).
          # Those tests (remote builds, chroot and overlay stores, ...)
          # then build with store paths that only exist inside a sandbox.
          substituteInPlace common/vars.sh --replace-fail \
            '&& unshare --user true; then' '&& false; then'
          popd >/dev/null
        '';
    });
    # Fil-C's libc has no vfork.
    nix-util = nprev.nix-util.overrideAttrs (old: {
      postPatch = (old.postPatch or "") + ''
                  substituteInPlace $(find . -path '*/unix/processes.cc') \
                    --replace-fail 'allowVfork ? vfork() : fork()' 'fork()'
                  # Nor clone, which the namespace probes use: report no user,
                  # mount or PID namespaces.
                  substituteInPlace $(find . -path '*/linux/linux-namespaces.cc') \
                    --replace-fail 'bool userNamespacesSupported()
        {' 'bool userNamespacesSupported()
        {
            return false;' \
                    --replace-fail 'bool mountAndPidNamespacesSupported()
        {' 'bool mountAndPidNamespacesSupported()
        {
            return false;'
      '';
    });
    nix-store =
      (nprev.nix-store.override {
        withSandboxShell = false;
        withAWS = false;
      }).overrideAttrs
        (old: {
          # Without seccomp, builds refuse to start unless filter-syscalls
          # is off, so make that the default.
          postPatch =
            (old.postPatch or "")
            + "\n"
            + ''
              f=$(find . -path '*/nix/store/local-settings.hh')
              sed -i '/Setting<bool> filterSyscalls{/,/"filter-syscalls"/ s/^\( *\)true,$/\1false,/' "$f"
              grep -A2 'Setting<bool> filterSyscalls{' "$f" | grep -q false,
            ''
            # Fil-C's loader ignores RUNPATH when dlopening a bare soname,
            # so name libc's nss_dns by path. NixOS's nix.conf check fails
            # on the warning otherwise.
            + ''
              substituteInPlace globals.cc --replace-fail \
                'dlopen(LIBNSS_DNS_SO,' \
                'dlopen("${final.stdenv.cc.libc}/lib/" LIBNSS_DNS_SO,'
            '';
          buildInputs = builtins.filter (
            dep: !(pkgs.lib.hasInfix "libseccomp" (dep.name or ""))
          ) old.buildInputs;
          mesonFlags = map (
            flag:
            if flag == "-Dseccomp-sandboxing=enabled" then
              "-Dseccomp-sandboxing=disabled"
            else
              flag
          ) old.mesonFlags;
        });
  };

  # A program from the Fil-C sysroot's glibc.
  libcTool =
    name:
    final.runCommand name { meta.mainProgram = name; } ''
      mkdir -p $out/bin
      ln -s ${final.stdenv.cc.libc}/bin/${name} $out/bin/${name}
    '';

  # Fil-C PHP 8.4 at a given release; see php84 below.
  mkFilcPhp84 =
    { version, hash }:
    let
      php =
        (
          (final.callPackage "${prev.path}/pkgs/development/interpreters/php" {
            llvmPackages = prev.llvmPackages // {
              inherit (final) stdenv;
            };
          }).php84.override
            {
              inherit version hash;
              # Bundled extensions build from the unpatched PHP source.
              packageOverrides =
                _: pprev:
                let
                  # Most PECL extensions build without their tests in Nixpkgs, and
                  # tests run with no other extension loaded (run-tests drops
                  # extension= lines from the ini), so tests that need session,
                  # json, ... skip. Load the default extensions and the
                  # extension's own dependencies ahead of it, and print the diff
                  # of each failure.
                  withTests =
                    ext:
                    ext.overrideAttrs (old: {
                      doCheck = true;
                      checkPhase = ''
                        runHook preCheck
                        sed -i "s|^PHP_TEST_SHARED_EXTENSIONS = |&$(
                          sed -n 's/^\(zend_\)\?extension=/-d &/p' ${
                            php.withExtensions (
                              { enabled, ... }: enabled ++ old.peclDeps or [ ] ++ old.internalDeps or [ ]
                            )
                          }/lib/php.ini | tr '\n' ' '
                        )|" Makefile
                        export NO_INTERACTION=1 SKIP_ONLINE_TESTS=1 SKIP_SLOW_TESTS=1 SKIP_PERF_SENSITIVE=1
                        # run-tests matches EXPECTF sections with PCRE, which has no
                        # JIT here, so lines with many %s exhausted the default
                        # backtrack limit and passing tests failed. run-tests
                        # itself runs with -n, its parallel workers with no
                        # options; the tests run with -n and see neither.
                        settings="PHP_TEST_SETTINGS=-d open_basedir= -d output_buffering=0 -d memory_limit=-1 -d pcre.backtrack_limit=100000000"
                        mkdir -p "$TMPDIR/run-tests-ini"
                        echo pcre.backtrack_limit=100000000 > "$TMPDIR/run-tests-ini/pcre.ini"
                        export PHP_INI_SCAN_DIR="$TMPDIR/run-tests-ini"
                        USE_ZEND_ALLOC=1 \
                          make "$settings" test TESTS="-j''${phpTestJobs:-$NIX_BUILD_CORES} -q --show-diff"
                        # Zend's allocator carves request memory out of 2 MiB
                        # chunks, so Fil-C bounds a PHP value by its chunk, and
                        # overflows and use after free between values go
                        # unnoticed. PHP defaults to the system allocator here
                        # (php-8.4-alloc-filc.patch), which gives each allocation
                        # its own bounds; run the tests on both. SKIP_ASAN
                        # skips the tests that need Zend's allocator, as in
                        # upstream's ASan runs, and zendAllocOnlyTests lists those
                        # that need it without saying so, like memory_limit tests.
                        rm -f ${toString (old.zendAllocOnlyTests or [ ])}
                        USE_ZEND_ALLOC=0 SKIP_ASAN=1 \
                          make "$settings" test TESTS="-j''${phpTestJobs:-$NIX_BUILD_CORES} -q --show-diff"
                        runHook postCheck
                      '';
                    });

                  # Drop tests that fail the same way without Fil-C or that need
                  # what the build sandbox lacks. Paths are relative to where
                  # postPatch runs: the PHP source for bundled extensions.
                  withoutTests =
                    files: ext:
                    ext.overrideAttrs (old: {
                      postPatch = (old.postPatch or "") + ''
                        rm ${toString files}
                      '';
                    });

                  # config.m4 looks up plain pkg-config, which a cross build
                  # only has under its target prefix.
                  withPkgConfig =
                    ext:
                    ext.overrideAttrs (old: {
                      preConfigure = (old.preConfigure or "") + ''
                        configureFlagsArray+=("ac_cv_path_PKG_CONFIG=$(command -v $PKG_CONFIG)")
                      '';
                    });

                  # Memcached servers on ports 11211 and 11212 for the tests.
                  withMemcached =
                    ext:
                    ext.overrideAttrs (old: {
                      # The tests share the servers.
                      phpTestJobs = 1;
                      preCheck = (old.preCheck or "") + ''
                        for port in 11211 11212; do
                          ${final.buildPackages.memcached}/bin/memcached -d -p $port -U 0 -u "$(id -un)"
                        done
                      '';
                    });
                in
                {
                  extensions =
                    pprev.extensions
                    // final.lib.genAttrs [
                      "bz2"
                      "dba"
                      "snmp"
                      "sysvmsg"
                      "sysvshm"
                      "tidy"
                      "xsl"
                      "zend_test"
                      "amqp"
                      "ast"
                      "decimal"
                      "ds"
                      "event"
                      "excimer"
                      "gnupg"
                      "igbinary"
                      "imap"
                      "inotify"
                      "mailparse"
                      "maxminddb"
                      "memcache"
                      "memcached"
                      "meminfo"
                      "msgpack"
                      "pcov"
                      "phalcon"
                      "pinba"
                      "protobuf"
                      "pspell"
                      "rdkafka"
                      "redis"
                      "snuffleupagus"
                      "spx"
                      "ssh2"
                      "systemd"
                      "uuid"
                      "uv"
                      "vld"
                      "wikidiff2"
                      "yaml"
                      "zstd"
                    ] (name: withTests pprev.extensions.${name})
                    // {
                      dom = pprev.extensions.dom.overrideAttrs (old: {
                        patches = (old.patches or [ ]) ++ [ ../patches/php-8.4-dom-filc.patch ];
                      });
                      filter = pprev.extensions.filter.overrideAttrs (
                        old:
                        final.lib.optionalAttrs (final.lib.versionAtLeast version "8.4.27") {
                          # These new OOM tests spawn CGI with -n, which omits
                          # Nixpkgs' shared filter module. Keep testing the OOM,
                          # not an undefined filter_input() function.
                          postPatch = (old.postPatch or "") + ''
                            substituteInPlace ext/filter/tests/oom_filter_{default_encoded,input,input_array}.phpt \
                              --replace-fail "'-n'," "'-n', '-d', 'extension=$PWD/ext/filter/modules/filter.so',"
                          '';
                        }
                      );
                      pcntl = pprev.extensions.pcntl.overrideAttrs (old: {
                        # Pins CPUs 0 and 1, but build sandboxes may exclude CPU 0.
                        postPatch = (old.postPatch or "") + ''
                          rm ext/pcntl/tests/pcntl_cpuaffinity.phpt
                        '';
                      });
                      # The format probes run programs, so the cross build assumed
                      # libgd had none of them; it has all of them.
                      gd = pprev.extensions.gd.overrideAttrs (old: {
                        configureFlags =
                          old.configureFlags
                          ++ map (f: "php_cv_lib_gd_gdImageCreateFrom${f}=yes") [
                            "Png"
                            "Avif"
                            "Webp"
                            "Jpeg"
                            "Xpm"
                            "Bmp"
                            "Tga"
                          ];
                      });
                      # Nixpkgs pins ICU 73; use the ported default ICU.
                      intl = pprev.extensions.intl.overrideAttrs { buildInputs = [ final.icu ]; };
                      opcache = pprev.extensions.opcache.overrideAttrs (old: {
                        patches =
                          (old.patches or [ ])
                          ++ [ ../patches/php-8.4-opcache-filc.patch ]
                          ++ final.lib.optional (final.lib.versionAtLeast version "8.4.27") ../patches/php-8.4-opcache-ce-cache-filc.patch;
                        # The JIT emits machine code, which Fil-C cannot run.
                        configureFlags = old.configureFlags ++ [ "--disable-opcache-jit" ];
                      });

                      # Bundled extensions outside the default set.
                      shmop = withTests (
                        pprev.extensions.shmop.overrideAttrs (old: {
                          patches = (old.patches or [ ]) ++ [ ../patches/php-8.4-shmop-filc.patch ];
                        })
                      );
                      ffi = withTests (
                        pprev.extensions.ffi.overrideAttrs (old: {
                          postPatch = (old.postPatch or "") + ''
                            # Frees a malloc() result rebuilt from its address as an
                            # integer, which has no capability; Fil-C stops it.
                            rm ext/ffi/tests/gh14626.phpt
                            # Tests that skip without libc.so.6; Fil-C's is .6666.
                            sed -i 's/libc\.so\.6\b/libc.so.6666/g' ext/ffi/tests/*.phpt
                          '';
                        })
                      );

                      # PECL extensions.
                      apcu = withTests (
                        pprev.extensions.apcu.overrideAttrs (old: {
                          patches = (old.patches or [ ]) ++ [ ../patches/php-apcu-filc.patch ];
                        })
                      );
                      # The version probe runs a program.
                      amqp = withTests (
                        pprev.extensions.amqp.overrideAttrs (old: {
                          configureFlags = (old.configureFlags or [ ]) ++ [
                            "ac_cv_librabbitmq_version=${final.rabbitmq-c.version}"
                          ];
                        })
                      );
                      # The tests share one GnuPG home directory.
                      gnupg = withTests (pprev.extensions.gnupg.overrideAttrs { phpTestJobs = 1; });
                      # The removed test predates PHP 8.2's dynamic property
                      # deprecation.
                      meminfo =
                        withoutTests [ "tests/bug-github-76_children_items_not_linked_php7.phpt" ]
                          (
                            withTests (
                              pprev.extensions.meminfo.overrideAttrs (old: {
                                patches = (old.patches or [ ]) ++ [ ../patches/php-meminfo-undef.patch ];
                              })
                            )
                          );
                      # Unix socket tests want /var/run/memcached; 056 wants a
                      # connection timeout where the sandbox has no route.
                      memcache = withMemcached (
                        withoutTests [ "tests/035.phpt" "tests/053.phpt" "tests/056.phpt" ] (
                          withTests pprev.extensions.memcache
                        )
                      );
                      # Fail the same way on x86-64 PHP without Fil-C.
                      memcached = withMemcached (
                        withPkgConfig (
                          withoutTests (map (t: "tests/${t}.phpt") [
                            "experimental/extreme_floats"
                            "experimental/getdelayed_cbthrows"
                            "experimental/get_udp"
                            "experimental/session_gc"
                            "experimental/setmulti_badserialize"
                            "experimental/stats_badserver"
                            "experimental/stats"
                            "fetchall_badunserialize"
                            "fetch_badunserialize"
                            "getdelayed_badunserialize"
                            "getmulti_badunserialize"
                            # Their SKIPIF includes a file the release lacks.
                            "experimental/serializer/serializer_php_bad_serialize"
                            "experimental/serializer/serializer_php_bad_unserialize"
                            "experimental/serializer_igbinary"
                            "experimental/serializer_json"
                          ]) (withTests pprev.extensions.memcached)
                        )
                      );
                      grpc = withPkgConfig (withTests pprev.extensions.grpc);
                      zstd = withPkgConfig (withTests pprev.extensions.zstd);
                      # The inotify probe runs a program; the header is enough.
                      inotify = withTests (
                        pprev.extensions.inotify.overrideAttrs (old: {
                          postPatch = (old.postPatch or "") + ''
                            sed -i 's/^  \])$/  ],[:])/' config.m4
                          '';
                        })
                      );
                      # Tests written before PHP 8.4's deprecation notices.
                      igbinary = withoutTests [
                        "tests/igbinary_009b_php8.phpt"
                        "tests/__serialize_020.phpt"
                      ] (withTests pprev.extensions.igbinary);
                      msgpack =
                        withoutTests
                          [
                            # Nixpkgs builds msgpack without session support.
                            "tests/015.phpt"
                            "tests/015b.phpt"
                            "tests/015e.phpt"
                            "tests/027.phpt"
                            "tests/028.phpt"
                            "tests/029.phpt"
                            "tests/issue132.phpt"
                            # Wants 400 unserializations a second, a native speed.
                            "tests/035.phpt"
                          ]
                          (
                            withTests (
                              pprev.extensions.msgpack.overrideAttrs (old: {
                                patches = (old.patches or [ ]) ++ [
                                  ../patches/php-msgpack-map-item-double-free.patch
                                  ../patches/php-msgpack-enum-refcount.patch
                                ];
                              })
                            )
                          );
                      # Judy keeps every node address in a Word_t (JudyMalloc
                      # returns one), so the pointers it hands back have no
                      # capability and the first allocation memprof records
                      # traps in JudyLIns. Porting needs Judy retyped throughout.
                      memprof = pprev.extensions.memprof.overrideAttrs (old: {
                        meta = old.meta // {
                          broken = true;
                        };
                      });
                      # Busy-waits on the wall clock and expects that much CPU
                      # time; it passes alone but not beside other test jobs.
                      luasandbox = withoutTests [ "tests/timer.phpt" ] (
                        withTests (
                          pprev.extensions.luasandbox.overrideAttrs {
                            zendAllocOnlyTests = [ "tests/oom-init.phpt" ];
                          }
                        )
                      );
                      opentelemetry = withTests (
                        pprev.extensions.opentelemetry.overrideAttrs (old: {
                          patches = (old.patches or [ ]) ++ [
                            ../patches/php-opentelemetry-hook-args-refcount.patch
                          ];
                        })
                      );
                      # Fail the same way on x86-64 PHP without Fil-C.
                      mongodb = withoutTests [ "tests/manager/manager-ctor-server.phpt" ] (
                        withTests pprev.extensions.mongodb
                      );
                      uv = withoutTests [ "tests/005-uv_listen_cb-not-destroyed.phpt" ] (
                        withTests pprev.extensions.uv
                      );
                      vld = withoutTests [
                        "tests/catch-php70.phpt"
                        "tests/foreach-jumps-php70.phpt"
                        "tests/issue00019-php70.phpt"
                        "tests/issue00020-01-php70-64bit.phpt"
                        "tests/issue00020-02-php70-64bit.phpt"
                        "tests/issue00021-php70.phpt"
                      ] (withTests pprev.extensions.vld);
                      # Opens compress.zlib://ext/xsl/tests/..., relative to the
                      # PHP source root rather than the extension.
                      xsl = withoutTests [ "ext/xsl/tests/xslt009.phpt" ] (
                        withTests pprev.extensions.xsl
                      );
                      # phpredis tests itself with a PHP script against servers
                      # on ports 6379 to 6382 rather than with run-tests.
                      redis = pprev.extensions.redis.overrideAttrs {
                        doCheck = true;
                        checkPhase = ''
                          runHook preCheck
                          for port in 6379 6380 6381 6382; do
                            ${final.buildPackages.redis}/bin/redis-server --port $port \
                              --save "" --appendonly no --daemonize yes
                          done
                          for _ in $(seq 100); do
                            ${final.buildPackages.redis}/bin/redis-cli -p 6382 ping && break
                            sleep 0.1
                          done
                          # These race a background PHP holding a session lock
                          # against fixed waits sized for native start-up; on
                          # busy builders different ones missed their windows.
                          for t in lockReleasedOnClose lockWaitTime lock_ttlLockExpire \
                            lock_ttlMaxExecutionTime lockHoldCheckBeforeWrite_otherProcessHasLock \
                            correctLockRetryCount defaultLockRetryCount; do
                            substituteInPlace tests/RedisTest.php \
                              --replace-fail "function testSession_$t(" "function skipSession_$t("
                          done
                          # Session tests run these in child processes.
                          export TEST_PHP_EXECUTABLE=${php}/bin/php
                          export TEST_PHP_ARGS="-d extension=$PWD/modules/redis.so"
                          # Also on the system allocator; see withTests.
                          for alloc in 1 0; do
                            for class in Redis RedisArray; do
                              USE_ZEND_ALLOC=$alloc ${php}/bin/php -d extension=$PWD/modules/redis.so \
                                tests/TestRedis.php --class $class --nocolors
                            done
                          done
                          for port in 6379 6380 6381 6382; do
                            ${final.buildPackages.redis}/bin/redis-cli -p $port shutdown nosave
                          done
                          runHook postCheck
                        '';
                      };
                      # The text tests need fonts and a fontconfig configuration,
                      # which the build sandbox lacks. The removed test fails the
                      # same way without Fil-C.
                      imagick = withoutTests [ "tests/024-ispixelsimilar.phpt" ] (
                        withTests (
                          pprev.extensions.imagick.overrideAttrs (old: {
                            preCheck = (old.preCheck or "") + ''
                              export FONTCONFIG_FILE=${
                                final.buildPackages.makeFontsConf {
                                  fontDirectories = [ final.buildPackages.dejavu_fonts ];
                                }
                              } XDG_CACHE_HOME=$TMPDIR/cache
                            '';
                          })
                        )
                      );
                      # Xdebug has its own copy of run-tests. Its debugger tests
                      # start PHP themselves, so load the extensions from an ini
                      # directory that every PHP started here reads.
                      xdebug = pprev.extensions.xdebug.overrideAttrs (old: {
                        patches = (old.patches or [ ]) ++ [
                          ../patches/php-xdebug-out-of-bounds.patch
                        ];
                        doCheck = true;
                        checkPhase = ''
                          runHook preCheck
                          mkdir ini
                          grep -E '^(zend_)?extension=' ${
                            php.withExtensions ({ enabled, ... }: enabled)
                          }/lib/php.ini > ini/extensions.ini
                          echo "zend_extension=$PWD/modules/xdebug.so" >> ini/extensions.ini
                          # For run-tests' workers; see withTests.
                          echo pcre.backtrack_limit=100000000 > ini/pcre.ini
                          export PHP_INI_SCAN_DIR=$PWD/ini TEST_PHP_EXECUTABLE=${php}/bin/php \
                            NO_INTERACTION=1 OPCACHE=no SKIP_SLOW_TESTS=1 SKIP_UNPARALLEL_TESTS=1 SKIP_ONLINE_TESTS=1
                          run() {
                            $TEST_PHP_EXECUTABLE -n -d pcre.backtrack_limit=100000000 \
                              run-xdebug-tests.php -j$NIX_BUILD_CORES -q --show-diff \
                              -d xdebug.mode=develop,debug,coverage,trace,profile "$@"
                          }
                          USE_ZEND_ALLOC=1 run tests
                          # Also on the system allocator; see withTests. Leave out
                          # the debugger tests there: some give the debugged PHP a
                          # second to connect, and on a busy builder one connected
                          # after the client had given up and both waited forever.
                          USE_ZEND_ALLOC=0 run $(ls -d tests/*/ | grep -v '^tests/debugger/$')
                          runHook postCheck
                        '';
                      });
                      snuffleupagus = withTests (
                        pprev.extensions.snuffleupagus.overrideAttrs (old: {
                          patches = (old.patches or [ ]) ++ [
                            ../patches/php-snuffleupagus-scanner-unsigned.patch
                          ];
                        })
                      );
                      # config.m4 never substitutes SPX_SHARED_LIBADD, so spx.so
                      # was not linked with zlib and only loaded after another
                      # module had brought it in.
                      # spx_custom_metadata fails the same way without Fil-C.
                      spx = withoutTests [ "tests/spx_custom_metadata.phpt" ] (
                        withTests (
                          pprev.extensions.spx.overrideAttrs (old: {
                            buildInputs = (old.buildInputs or [ ]) ++ [ final.zlib ];
                            makeFlags = (old.makeFlags or [ ]) ++ [ "SPX_SHARED_LIBADD=-lz" ];
                          })
                        )
                      );
                    };
                };
            }
        ).overrideAttrs
          (old: {
            patches = old.patches ++ [
              ../patches/php-8.4-filc.patch
              # Default to the system allocator so Fil-C bounds each PHP value.
              ../patches/php-8.4-alloc-filc.patch
            ];
            # Adds -Wa,--compress-debug-sections, which SaRCAsm rejects.
            separateDebugInfo = false;
            configureFlags = old.configureFlags ++ [
              # Fibers switch stacks with ucontext, like Boost.Context here,
              # instead of the fcontext assembly.
              "--disable-fiber-asm"
              # Overflow-checked arithmetic in C instead of x86 `asm goto`,
              # whose callbr crashes FilPizlonatorPass.
              "php_cv_have__asm_goto=no"
              # Fil-C cannot run generated machine code; PCRE warned at the
              # first preg_* call when mapping executable memory failed.
              "--without-pcre-jit"
              # phpdbg's watchpoints would use userfaultfd, which Fil-C does not
              # support; phpdbg died at startup.
              "ac_cv_have_decl_UFFDIO_WRITEPROTECT_MODE_WP=no"
              # The probe runs a program, so the cross build disabled the stack
              # limit check; deep recursion then hit Fil-C's stack overflow trap
              # instead of throwing "Maximum call stack size reached".
              "php_cv_have_stack_limit=yes"
            ];
          });
    in
    php;
in
portDSL.makeOverlay portList final prev
// pkgs.lib.optionalAttrs prev.stdenv.hostPlatform.isFilc {
  # libunwind's unwinder is hand-written assembly without SaRCAsm
  # annotations, and cannot follow Fil-C frames anyway. Packages that check
  # availability (GStreamer, strace, ...) then build without it.
  libunwind = prev.libunwind.overrideAttrs (old: {
    meta = old.meta // {
      badPlatforms = (old.meta.badPlatforms or [ ]) ++ [
        prev.stdenv.hostPlatform.system
      ];
    };
  });

  # Boost 1.87 is the ported release (Context uses ucontext); Nixpkgs'
  # default 1.89 builds its assembly fcontext and fails.
  boost = final.boost187;

  # Nixpkgs builds PHP with llvmPackages.stdenv whenever the compiler is
  # Clang, which for Fil-C means a second compiler-rt and libc++ (and a
  # cross GCC) built from source. The Fil-C stdenv is already Clang.
  #
  # php84 follows PHP's releases; php84_25 keeps 8.4.25, the release the
  # unserialize() var_destroy use-after-free reproduction ran against
  # (docs/php.md), for comparing exploits and fixes.
  php84 = mkFilcPhp84 {
    version = "8.4.27";
    hash = "sha256-slMKh3xyL0sIyeF0owywi6wrfhkD7m6eMV8KqfX4LCQ=";
  };
  php84_25 = mkFilcPhp84 {
    version = "8.4.25";
    hash = "sha256-lSzMF4Uma5WPSh3PxYDgjqu7efRCItHv8ZK82Y2R9uM=";
  };

  # PHP 7.4, from fossar/nix-phps, which keeps Nixpkgs' PHP builder working
  # for releases Nixpkgs has dropped. See docs/php.md.
  php74 =
    let
      nixPhps = builtins.fetchTarball {
        url = "https://github.com/fossar/nix-phps/archive/9fb06f7d8beb2ec686fc20b9bf7fe7ce25a429a6.tar.gz";
        sha256 = "1p5bvrs9psm4a26bp420902b1i8qa3wz8s8avmrcizrr3d4h0qza";
      };
      phps = import "${nixPhps}/pkgs/phps.nix" prev.path final prev;
      # Bundled extensions build from the unpatched PHP source.
      filcOverrides = _: pprev: {
        extensions = pprev.extensions // {
          # The probes run programs, so the cross build assumed an iconv
          # without errno that honours //IGNORE; glibc's sets errno and
          # fails on //IGNORE.
          iconv = pprev.extensions.iconv.overrideAttrs (old: {
            postPatch = (old.postPatch or "") + ''
              sed -i 's/\(ICONV_SUPPORTS_ERRNO\|ICONV_BROKEN_IGNORE\)\],0/\1],1/' \
                ext/iconv/config.m4
            '';
          });
          opcache = pprev.extensions.opcache.overrideAttrs (old: {
            patches = (old.patches or [ ]) ++ [ ../patches/php-7.4-opcache-filc.patch ];
            # The shared memory probes run programs, so the cross build
            # found none and opcache could not start. Anonymous mmap works.
            env = (old.env or { }) // {
              NIX_CFLAGS_COMPILE =
                (old.env.NIX_CFLAGS_COMPILE or "") + " -DHAVE_SHM_MMAP_ANON=1";
            };
            # Expects mapping 1 GB of shared memory to fail; the private
            # mapping that replaces it succeeds.
            postPatch = (old.postPatch or "") + ''
              rm ext/opcache/tests/log_verbosity_bug.phpt
            '';
          });
        };
      };
    in
    (phps.php74.override {
      # Replaces nix-phps' own overrides, so apply those first.
      packageOverrides = final.lib.composeExtensions (import "${nixPhps}/pkgs/package-overrides.nix" prev) filcOverrides;
    }).overrideAttrs
      (old: {
        patches = old.patches ++ [
          ../patches/php-7.4-filc.patch
          # Default to the system allocator so Fil-C bounds each PHP value.
          ../patches/php-7.4-alloc-filc.patch
        ];
        # Adds -Wa,--compress-debug-sections, which SaRCAsm rejects.
        separateDebugInfo = false;
        configureFlags = old.configureFlags ++ [
          # Overflow-checked arithmetic in C instead of x86 `asm goto`.
          "ac_cv__asm_goto=no"
          # Fil-C cannot run generated machine code.
          "--without-pcre-jit"
          # Probes that run programs, which the cross build cannot.
          "ac_cv_func_getaddrinfo=yes"
          "ac_cv_func_fnmatch_works=yes"
          "php_cv_sizeof_intmax_t=8"
        ];
      });

  # The ODBC driver builds its bundled Connector/C submodule, whose export
  # map needs the same fix as mariadb-connector-c (see ports.nix).
  unixodbcDrivers = prev.unixodbcDrivers // {
    mariadb = prev.unixodbcDrivers.mariadb.overrideAttrs (old: {
      postPatch = (old.postPatch or "") + ''
        patch -p1 -d libmariadb < ${../patches/mariadb-connector-c-version-script.patch}
      '';
    });
  };

  # Node.js (V8) is out of scope. Small pure-JS CLIs run on QuickJS through
  # the qnode shim instead; see docs/quickjs-for-node.md.
  qnode = final.callPackage ../packages/qnode { };
  bibtex-tidy = final.callPackage ../packages/qnode/npm-cli.nix { } {
    package = final.buildPackages.bibtex-tidy;
    bins.bibtex-tidy = "bibtex-tidy/bin/bibtex-tidy";
  };
  aasvg = final.callPackage ../packages/qnode/npm-cli.nix { } {
    package = final.buildPackages.aasvg;
    bins.aasvg = "aasvg/main.js";
  };

  # YouTube needs a JavaScript runtime; yt-dlp's default, Deno, is V8.
  # QuickJS is one of its supported runtimes. curl-cffi (curl-impersonate
  # needs Go) and secretstorage (cryptography needs Rust) are optional.
  # pycryptodomex is optional too (yt-dlp has a pure-Python AES), and the
  # build's native Python would dlopen its Fil-C ctypes library and fail.
  yt-dlp =
    (prev.yt-dlp.override {
      # The top-level python3Packages argument splices to the build
      # platform's default Python (3.13), whose hatchling the Fil-C
      # Python 3.12 build cannot import. Use the ported set directly.
      python3Packages = final.python3Packages;
      jsRuntime = final.quickjs;
      withSecretStorage = false;
    }).overridePythonAttrs
      (old: {
        dependencies = builtins.filter (
          d:
          !builtins.elem (d.pname or "") [
            "curl-cffi"
            "pycryptodomex"
          ]
        ) old.dependencies;
      });

  # The pnpm dependency fetcher's output is platform-independent, but it
  # overrides pnpm-fixup-state-db with pnpm's own Node.js, which loses
  # splicing and pulls in the host (Fil-C) Node.js. Run it natively.
  fetchPnpmDeps = prev.lib.makeOverridable (
    args:
    final.buildPackages.fetchPnpmDeps (
      args
      // prev.lib.optionalAttrs (args ? pnpm) {
        pnpm = args.pnpm.__spliced.buildHost or args.pnpm;
      }
    )
  );

  # overrideScope, so that the plugins build against this GStreamer.
  gst_all_1 = prev.gst_all_1.overrideScope (
    gfinal: gprev: {
      # Only the optional PTP clock helper uses Rust. The multimedia core is C.
      gstreamer =
        (gprev.gstreamer.override {
          withRust = false;
          # Native stack unwinding does not understand Fil-C frames.
          withLibunwind = false;
        }).overrideAttrs
          (
            old:
            (import ../toolchain/meson-check-cores.nix { inherit pkgs; }) old
            // {
              patches = (old.patches or [ ]) ++ [
                ./patch/gstreamer-1.24.7.patch
                ../patches/gstreamer-execinfo.patch
              ];
              doCheck = true;
              env = (old.env or { }) // {
                CK_TIMEOUT_MULTIPLIER = "5";
              };
            }
          );
      # GType is a pointer in Fil-C's GLib; upstream Fil-C's 1.24.7 patch,
      # rebased onto 1.26.
      gst-plugins-base = gprev.gst-plugins-base.overrideAttrs (old: {
        patches = (old.patches or [ ]) ++ [
          ./patch/gst-plugins-base-1.26.11.patch
        ];
      });
      gst-plugins-good = gprev.gst-plugins-good.overrideAttrs (old: {
        # Pointer GTypes: pointer once-inits, switches on uintptr_t, and
        # signal parameters without G_SIGNAL_TYPE_STATIC_SCOPE bits.
        patches = (old.patches or [ ]) ++ [
          ../patches/gst-plugins-good-gtype.patch
        ];
        # The deinterlacer's x86 assembly.
        mesonFlags = old.mesonFlags ++ [ "-Dasm=disabled" ];
      });
    }
  );

  linphonePackages = prev.linphonePackages.overrideScope (
    lfinal: lprev: {
      # Python generates sources at build time. As a build input it was
      # the Fil-C Python, which CMake's FindPython3 does not accept as the
      # build machine's interpreter.
      bc-decaf = lprev.bc-decaf.overrideAttrs (old: {
        patches = (old.patches or [ ]) ++ [
          ../patches/bc-decaf-filc-x86-asm.patch
        ];
        nativeBuildInputs = old.nativeBuildInputs ++ [ pkgs.python3 ];
        buildInputs = [ ];
        doCheck = true;
      });
    }
  );

  # See ports/qt5.nix.
  qt5 = prev.qt5.overrideScope (import ./qt5.nix { inherit pkgs final; });

  qt6 = prev.qt6.overrideScope (import ./qt6.nix { inherit pkgs final; });

  # Nix itself.
  nixComponents = prev.nixVersions.nixComponents_2_34.overrideScope (
    pkgs.lib.composeExtensions nixFilcOverrides (
      nfinal: nprev: {
        nix-expr =
          (nprev.nix-expr.override { enableGC = false; }).overrideAttrs
            (old: {
              # The 64-bit Value layout packs tag bits into pointers held as
              # integers, which drops their capabilities; use the plain one.
              postPatch =
                (old.postPatch or "")
                + "\n"
                + ''
                  substituteInPlace $(find . -path '*/nix/expr/value.hh') --replace-fail \
                    'useBitPackedValueStorage = (ptrSize == 8)' \
                    'useBitPackedValueStorage = false && (ptrSize == 8)'
                '';
            });
        # nativeBuildInputs' perl splices to the build platform's perl, which
        # cannot load the Fil-C DBI; Fil-C programs run on the build machine.
        nix-perl-bindings = nprev.nix-perl-bindings.overrideAttrs (old: {
          nativeBuildInputs = map (
            p: if (p.pname or "") == "perl" then final.perl else p
          ) old.nativeBuildInputs;
          nativeCheckInputs = [ final.perlPackages.Test2Harness ];
          # sv_setref_pv stores the wrapper through Fil-C's XS pointer table;
          # the typemap read it back with a cast.
          postPatch =
            (old.postPatch or "")
            + "\n"
            + ''
              substituteInPlace $(find . -path '*/lib/Nix/Store.xs') --replace-fail \
                '$var = ($type)SvIV((SV*)SvRV( $arg ));' \
                '$var = ($type) zptrtable_decode(Perl_xsub_ptrtable, SvIV((SV*)SvRV( $arg )));'
            '';
        });
      }
    )
  );
  nix = final.nixComponents.nix-everything;

  # Determinate Systems' fork; see ports/determinate-nix.nix.
  determinateNixComponents = import ./determinate-nix.nix {
    inherit pkgs final nixFilcOverrides;
  };
  determinate-nix = final.determinateNixComponents.nix-everything;

  # Boehm GC's API on Fil-C's own collector (docs/boehm-on-fugc.md).
  boehmgc = final.callPackage ./boehmgc { inherit (prev) boehmgc; };

  # unixtools takes glibc's getent and getconf only when libc is "glibc", and
  # NetBSD's otherwise, which do not evaluate here. The Fil-C sysroot has
  # glibc's.
  getent = libcTool "getent";
  getconf = libcTool "getconf";
  unixtools = prev.unixtools // {
    inherit (final) getent getconf;
  };

  # The emacs30 port has no GUI; the -nox variants come from Nixpkgs' Emacs
  # scope and would miss the port (and bring native compilation along).
  emacs-nox = final.emacs30;
  emacs30-nox = final.emacs30;

  tree-sitter = final.callPackage ./tree-sitter.nix {
    inherit (prev) tree-sitter;
  };

  # jemalloc's API on Fil-C's own allocator (docs/jemalloc-on-fugc.md).
  jemalloc = final.callPackage ./jemalloc { inherit (prev) jemalloc; };
}
