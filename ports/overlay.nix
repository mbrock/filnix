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
