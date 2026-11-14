# Qt 6 for Fil-C. Check with:
#   nix build -L --impure --expr 'import ./tests/qt6.nix { }'
{ pkgs, final }:
qfinal: qprev: {
  # CMake's cross-build check also applies to modules built against qtbase.
  qtModule =
    args:
    qprev.qtModule (
      args
      // {
        cmakeFlags = (args.cmakeFlags or [ ]) ++ [
          "-DQT_HOST_PATH=${pkgs.qt6.qtbase}"
        ];
      }
    );

  # Nixpkgs supplies imageformat dependencies here, but QtSvg only links
  # QtCore, QtGui and zlib (already propagated by qtbase). Jasper pulls in
  # an unrelated libheif/Rust/cross-GCC toolchain.
  qtsvg = qprev.qtsvg.overrideAttrs { buildInputs = [ ]; };

  qtshadertools = qprev.qtshadertools.overrideAttrs (old: {
    cmakeFlags = old.cmakeFlags ++ [
      "-DQt6ShaderToolsTools_DIR=${pkgs.qt6.qtshadertools}/lib/cmake/Qt6ShaderToolsTools"
    ];
  });

  qtdeclarative = qprev.qtdeclarative.overrideAttrs (old: {
    patches = old.patches ++ [ ../patches/qt6-declarative-filc.patch ];
    cmakeFlags = old.cmakeFlags ++ [
      "-DQT_FEATURE_qml_jit=OFF"
      "-DQt6QmlTools_DIR=${pkgs.qt6.qtdeclarative}/lib/cmake/Qt6QmlTools"
      "-DQt6QuickTools_DIR=${pkgs.qt6.qtdeclarative}/lib/cmake/Qt6QuickTools"
      "-DQt6ShaderToolsTools_DIR=${pkgs.qt6.qtshadertools}/lib/cmake/Qt6ShaderToolsTools"
      "-DQT_FEATURE_quick=ON"
    ];
  });

  qtbase =
    (qprev.qtbase.override {
      # The Fil-C GTK 3 port has no X11 backend (gdk/gdkx.h).
      withGtk3 = false;
      # Same X11-enabled dependency as Qt 5. Its Xvfb tests use unsupported
      # __start_/__stop_ section symbols, so omit those tests, not the backend.
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
      # Fil-C programs can run on the build machine, but this is still a
      # cross build. Do not pull translations and their target qttools into
      # qtbase; use the native tools explicitly below.
      qttranslations = null;
    }).overrideAttrs
      (old: {
        patches = old.patches ++ [
          ../patches/qt6-base-filc.patch
          ../patches/qt6-container-rotate-filc.patch
          # forkfd_wait() probes raw waitid even with FFD_USE_FORK.
          ../patches/qt5-forkfd-fork.patch
        ];
        cmakeFlags = old.cmakeFlags ++ [
          "-DQT_HOST_PATH=${pkgs.qt6.qtbase}"
          "-DQt6HostInfo_DIR=${pkgs.qt6.qtbase}/lib/cmake/Qt6HostInfo"
          # .symver module assembly is unsupported by Fil-C.
          "-DQT_FEATURE_version_tagging=OFF"
          # The small configure probe passes, but Qt's generated script
          # uses character-class globs that Fil-C's driver cannot parse.
          "-DHAVE_LD_VERSION_SCRIPT=OFF"
          # QProcess must use fork(), not vfork()/clone(CLONE_PIDFD).
          "-DQT_FEATURE_forkfd_pidfd=OFF"
        ];
      });
}
