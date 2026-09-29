# Qt 5.15 for Fil-C, as an override of the qt5 scope (libsForQt5 is
# built from final.qt5, so its packages see these modules too).
{ pkgs, final }:
qfinal: qprev: {
  qtbase =
    (qprev.qtbase.override {
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
}
