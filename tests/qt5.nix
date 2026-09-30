# Build small Qt 5 programs with the Fil-C qmake and run them on the
# offscreen platform and on X11 (a native Xvfb).
{
  source ? ../.,
  # Also build and run the SVG, QML and Qt Quick program.
  withQuick ? true,
}:
let
  pkgs =
    (builtins.getFlake (toString source)).legacyPackages.x86_64-linux.pkgsFilc;
  # Unspliced: in nativeBuildInputs a spliced qtbase.dev would become the
  # build platform's qtbase.
  qt5 = pkgs.pkgsHostTarget.qt5;
  inherit (qt5.qtbase) qtPluginPrefix qtQmlPrefix;
in
pkgs.stdenv.mkDerivation {
  pname = "qt5-smoke-check";
  version = "1";
  dontUnpack = true;
  dontWrapQtApps = true;
  # qtbase.dev carries qmake and moc (build-machine programs) and the
  # Fil-C mkspecs.
  nativeBuildInputs = [
    qt5.qtbase.dev
    pkgs.pkgsBuildBuild.xvfb-run
  ];
  buildInputs = [
    qt5.qtbase
  ]
  ++ pkgs.lib.optionals withQuick [
    qt5.qtsvg
    qt5.qtdeclarative
    qt5.qtquickcontrols2
  ];
  configurePhase = ''
    runHook preConfigure
    cp ${./qt5-smoke.cpp} qt5-smoke.cpp
    cp ${./qt5-quick.cpp} qt5-quick.cpp
    cat > smoke.pro <<'EOF'
    QT += widgets network sql xml concurrent testlib
    CONFIG += console
    SOURCES = qt5-smoke.cpp
    TARGET = qt5-smoke
    EOF
    cat > quick.pro <<'EOF'
    QT += svg qml quick
    CONFIG += console
    SOURCES = qt5-quick.cpp
    TARGET = qt5-quick
    EOF
    export QMAKEPATH=${
      pkgs.lib.concatMapStringsSep ":" (m: "${m.dev}") [
        qt5.qtsvg
        qt5.qtdeclarative
      ]
    }
    mkdir smoke quick
    (cd smoke && qmake ../smoke.pro)
    ${pkgs.lib.optionalString withQuick "(cd quick && qmake ../quick.pro)"}
    runHook postConfigure
  '';
  buildPhase = ''
    make -C smoke -j$NIX_BUILD_CORES
    ${pkgs.lib.optionalString withQuick "make -C quick -j$NIX_BUILD_CORES"}
  '';
  doCheck = true;
  checkPhase = ''
    export QT_PLUGIN_PATH=${qt5.qtbase.bin}/${qtPluginPrefix}
  ''
  + pkgs.lib.optionalString withQuick ''
    QT_PLUGIN_PATH+=:${qt5.qtsvg.bin}/${qtPluginPrefix}:${qt5.qtdeclarative.bin}/${qtPluginPrefix}
    export QML2_IMPORT_PATH=${qt5.qtdeclarative.bin}/${qtQmlPrefix}:${qt5.qtquickcontrols2.bin}/${qtQmlPrefix}
  ''
  + ''
    export QT_QUICK_BACKEND=software
    export FONTCONFIG_FILE=${
      pkgs.makeFontsConf { fontDirectories = [ pkgs.pkgsBuildBuild.dejavu_fonts ]; }
    }
    export HOME=$TMPDIR
    for platform in offscreen xcb; do
      for program in smoke/qt5-smoke ${pkgs.lib.optionalString withQuick "quick/qt5-quick"}; do
        echo "== $program on $platform"
        if [ $platform = xcb ]; then
          QT_QPA_PLATFORM=xcb xvfb-run -a -s "-screen 0 640x480x24" ./$program
        else
          QT_QPA_PLATFORM=$platform ./$program
        fi
      done
    done
  '';
  installPhase = ''
    mkdir -p $out/bin
    cp smoke/qt5-smoke ${pkgs.lib.optionalString withQuick "quick/qt5-quick"} $out/bin/
  '';
}
