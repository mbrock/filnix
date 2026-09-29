# Qt 5.15 for Fil-C, as an override of the qt5 scope (libsForQt5 is
# built from final.qt5, so its packages see these modules too).
{ pkgs, final }:
qfinal: qprev:
let
  inherit (pkgs) lib;
  # qtModule puts the scope's qmake hook in nativeBuildInputs, where
  # splicing picks the build platform's: that hook propagates the native
  # qtbase, and the module's setup hooks then fail with "detected
  # mismatched Qt dependencies". Use this scope's own hook, which adds
  # the Fil-C qtbase (whose qmake and moc are build-platform programs).
  qmakeHook = qfinal.qmake.__spliced.hostTarget or qfinal.qmake;
  withFilcQmake =
    drv:
    drv.overrideAttrs (old: {
      nativeBuildInputs = map (
        d: if (d.name or "") == "qmake-hook" then qmakeHook else d
      ) (old.nativeBuildInputs or [ ]);
    });
  # Qt modules' build tools (qtdeclarative's qmlcachegen and
  # qmltyperegistrar, native programs in its dev output) are looked up on
  # PATH, where a cross build has only the build platform's Qt.
  withQtToolsOnPath =
    drv:
    drv.overrideAttrs (old: {
      preConfigure = ''
        for p in "''${pkgsHostTarget[@]}"; do
          if [ -d "$p/mkspecs" ] && [ -d "$p/bin" ]; then addToSearchPath PATH "$p/bin"; fi
        done
      '' + (old.preConfigure or "");
    });
  modules = [
    "qt3d"
    "qtcharts"
    "qtconnectivity"
    "qtdatavis3d"
    "qtgamepad"
    "qtgraphicaleffects"
    "qtimageformats"
    "qtlocation"
    "qtlottie"
    "qtmultimedia"
    "qtnetworkauth"
    "qtpositioning"
    "qtpurchasing"
    "qtquick3d"
    "qtquickcontrols"
    "qtquickcontrols2"
    "qtremoteobjects"
    "qtscript"
    "qtscxml"
    "qtsensors"
    "qtserialbus"
    "qtserialport"
    "qtspeech"
    "qtsvg"
    "qtsystems"
    "qtvirtualkeyboard"
    "qtwayland"
    "qtwebchannel"
    "qtwebglplugin"
    "qtwebsockets"
    "qtx11extras"
    "qtxmlpatterns"
  ];
in
lib.genAttrs modules (name: withQtToolsOnPath (withFilcQmake qprev.${name}))
// {
  # qtdeclarative depends on it; keep it unchanged so qtdeclarative
  # (a long build) is not rebuilt for this.
  qtsvg = withFilcQmake qprev.qtsvg;
}
// {
  # qtbase's setup hook collects mkspecs for QMAKEPATH only from
  # nativeBuildInputs, which in a cross build are the build platform's; a
  # module's Qt dependencies (qtdeclarative for qtquickcontrols2, say) are
  # buildInputs, so qmake did not see them ("Some of the required modules
  # (qtHaveModule(quick)) are not available. Skipped."). Collect them too.
  qmake = qprev.qmake.overrideAttrs (old: {
    buildCommand = old.buildCommand + ''
      cat >> $out/nix-support/setup-hook <<'EOF'
      filcQmakeHostPathHook() {
          if declare -F qmakePathHook >/dev/null; then qmakePathHook "$1"; fi
      }
      addEnvHooks "$targetOffset" filcQmakeHostPathHook
      EOF
    '';
  });

  qtbase =
    (qprev.qtbase.override {
      # The GTK 3 port has no X11 backend, and Qt's GTK 3 platform theme
      # (native file dialogs and styling) includes <gdk/gdkx.h>.
      withGtk3 = false;
      # The xcb platform plugin needs libxkbcommon-x11, which the shared
      # libxkbcommon port leaves out (-Denable-x11=false). Its X11 tests
      # (which need Xvfb) find their cases through __start_/__stop_ section
      # symbols, which do not link under Fil-C, so leave those out.
      libxkbcommon = final.libxkbcommon.overrideAttrs (old: {
        mesonFlags = map (
          f: if f == "-Denable-x11=false" then "-Denable-x11=true" else f
        ) old.mesonFlags;
        postPatch = (old.postPatch or "") + ''
          substituteInPlace meson.build --replace-fail \
            "if get_option('enable-x11')
              has_xvfb" \
            "if false
              has_xvfb"
        '';
      });
    }).overrideAttrs
      (old: {
        patches = old.patches ++ [
          # Qt refuses pkg-config in a cross build without a sysroot, and a
          # sysroot of / turns -L/nix/store/... into -L//nix/store/..., which
          # the compiler wrapper then drops as an impure path.
          ../patches/qt5-pkg-config-no-sysroot.patch
          # Every file that includes <QtCore> outside QtCore emits a
          # .qtversion section as module-level assembly, which crashes the
          # Fil-C compiler. The header is installed, so this covers users too.
          ../patches/qt5-no-version-tagging.patch
          # QtCore's CPU feature probe saves %rbx around CPUID and spells
          # XGETBV as bytes; Fil-C only lowers the canonical forms. RDRAND
          # has no lowering, so leave it to the kernel's generator. Its Valgrind
          # check is a client request (inline assembly), which stops too.
          ../patches/qt5-cpu-probe.patch
          # QProcess's forkfd probes waitid(P_PIDFD) and clone(CLONE_PIDFD)
          # through syscall(), which Fil-C refuses by stopping the program.
          ../patches/qt5-forkfd-fork.patch
          # QMutexLocker, QReadLocker and QWriteLocker keep their lock's
          # address in a quintptr with a "locked" bit, QMap nodes their parent
          # with the colour bit, and QModelIndex its internal pointer. Integer
          # fields lose the capability, so these are pointers now.
          ../patches/qt5-pointer-fields.patch
          # QByteArray/QString::fromRawData point their header at the data
          # with an offset from the header, so data() had the header's
          # bounds; raw-data headers keep the data pointer instead.
          ../patches/qt5-raw-data.patch
          # Fil-C ignores section attributes on data, so plugins have no
          # .qtmetadata section; find the metadata in the whole file.
          ../patches/qt5-plugin-metadata.patch
          # QThread names threads with prctl(PR_SET_NAME, (unsigned long)name);
          # the integer has no capability, so the runtime's prctl trapped.
          ../patches/qt5-thread-name.patch
          # QSemaphore wakes with FUTEX_WAKE_OP, which Fil-C's futex refuses.
          ../patches/qt5-semaphore-futex.patch
        ];
        # Nixpkgs configures a cross qtbase with the linux-generic-g++ device
        # spec and CROSS_COMPILE=${targetPrefix}. Fil-C's compiler has no
        # target prefix, and the spec refuses an empty CROSS_COMPILE. Point
        # it at the wrapper's bin directory instead; the wrapper has ar, nm,
        # objcopy and strip there, and cc and c++ rather than gcc and g++.
        # The compiler is Clang, which prints no LIBRARY_PATH for qmake's
        # default-library-path probe; as `clang`, qmake asks
        # -print-search-dirs.
        configureFlags = map (
          f: if f == "CROSS_COMPILE=" then "CROSS_COMPILE=${final.stdenv.cc}/bin/" else f
        ) old.configureFlags;
        preConfigure = old.preConfigure + ''
          cat >> mkspecs/devices/linux-generic-g++/qmake.conf <<'EOF'
          QMAKE_COMPILER          = gcc clang llvm
          QMAKE_CC                = $${CROSS_COMPILE}cc
          QMAKE_CXX               = $${CROSS_COMPILE}c++
          QMAKE_LINK              = $${QMAKE_CXX}
          QMAKE_LINK_SHLIB        = $${QMAKE_CXX}
          QMAKE_LINK_C            = $${QMAKE_CC}
          QMAKE_LINK_C_SHLIB      = $${QMAKE_CC}
          EOF
        '';
      });

  qtdeclarative = (withFilcQmake qprev.qtdeclarative).overrideAttrs (old: {
    # The V4 engine NaN-boxes heap pointers into quint64 values and passes
    # them around as integers (ReturnedValue), which drops their
    # capabilities; keep them pointer-typed. Also QJSValue, PropertyKey,
    # QFlagPointer/QBiPointer, QQmlNotifierEndpoint and sparse-array nodes,
    # which keep pointers with flag bits in integers.
    patches = old.patches ++ [ ../patches/qt5-declarative-v4-pointers.patch ];
    # The V4 JIT writes machine code at run time; use the interpreter.
    qmakeFlags = (old.qmakeFlags or [ ]) ++ [
      "--"
      "-no-feature-qml-jit"
    ];
  });

  qttools = (withQtToolsOnPath (withFilcQmake qprev.qttools)).overrideAttrs (old: {
    # libclang and libllvm are only for qdoc, which Qt then leaves out;
    # they would be a Fil-C build of LLVM.
    buildInputs = [ ];
    patches = builtins.filter (
      p: !pkgs.lib.hasInfix "libclang-main-header" (toString p)
    ) old.patches;
  });
}
