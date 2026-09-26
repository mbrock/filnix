# Overlay for Fil-C ported packages
# Converts the port list from ../ports.nix into a nixpkgs overlay

pkgs: final: prev:
let
  portDSL = import ./default.nix { inherit (pkgs) lib pkgs; };
  portList = import ../ports.nix { inherit pkgs prev final; };
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

  # Nix itself. Boehm GC scans the native stack and data segments, which
  # Fil-C objects do not live in; Fil-C collects garbage itself. seccomp
  # filters and the static busybox sandbox shell are unavailable too.
  nixComponents = prev.nixVersions.nixComponents_2_34.overrideScope (
    nfinal: nprev: {
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
      nix-functional-tests = nprev.nix-functional-tests.overrideAttrs (old: {
        # The test plugin cannot resolve Nix's symbols when dlopened.
        mesonCheckFlags = (old.mesonCheckFlags or [ ]) ++ [
          "--no-suite"
          "plugins"
        ];
      });
      nix-util-tests = nprev.nix-util-tests.overrideAttrs (old: {
        # The CompressionError from invalid bzip2 input is freed while the
        # test's catch is still unwinding to it (docs/filc-findings.md).
        excludedTestPatterns = old.excludedTestPatterns ++ [
          "decompress.decompressInvalidInputThrowsCompressionError"
        ];
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
              ''
              # The pinned runtime traps on mount's NULL source and lacks
              # PR_GET_PDEATHSIG (fixed in mbrock/fil-c 6876dcb, 347ed5b). A
              # remount ignores the source, and startProcess set SIGKILL as
              # the death signal. Drop these with the next pin bump.
              + ''
                substituteInPlace local-store.cc --replace-fail \
                  'mount(0, config->realStoreDir' \
                  'mount("", config->realStoreDir'
                substituteInPlace unix/build/derivation-builder.cc --replace-fail \
                  'throw SysError("getting death signal");' \
                  'oldDeathSignal = SIGKILL;'
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
    }
  );
  nix = final.nixComponents.nix-everything;

  tree-sitter = final.callPackage ./tree-sitter.nix {
    inherit (prev) tree-sitter;
  };

  # The scanner executes C dumpers and loads a Python C extension; GLib's
  # gdbus-codegen emits GType operations. Both must match the target GLib ABI
  # even though they run during builds. Explicit scope overrides still win,
  # and the native package set keeps its ordinary tools. Package-set
  # attributes are spliced, so drop __spliced: mkDerivation would otherwise
  # swap in the build platform's tools for nativeBuildInputs.
  newScope =
    extra:
    prev.newScope (
      {
        gobject-introspection = removeAttrs final.gobject-introspection [
          "__spliced"
        ];
        glib = removeAttrs final.glib [ "__spliced" ];
        # mkenums_simple embeds C templates independently of glib-mkenums.
        meson = import ../toolchain/meson-filc.nix { inherit pkgs; };
      }
      // extra
    );
}
