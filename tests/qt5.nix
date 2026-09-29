# Build a small Qt 5 program with the Fil-C qmake and run it on the
# offscreen platform and on X11 (Xvfb).
{
  source ? ../.,
}:
let
  pkgs =
    (builtins.getFlake (toString source)).legacyPackages.x86_64-linux.pkgsFilc;
  qt5 = pkgs.qt5;
in
pkgs.stdenv.mkDerivation {
  pname = "qt5-smoke-check";
  version = "1";
  dontUnpack = true;
  # qtbase.dev carries qmake and moc (build-machine programs) and the
  # Fil-C mkspecs.
  nativeBuildInputs = [
    qt5.qtbase.dev
    pkgs.pkgsBuildBuild.xvfb-run
  ];
  buildInputs = [ qt5.qtbase ];
  configurePhase = ''
    runHook preConfigure
    cp ${./qt5-smoke.cpp} qt5-smoke.cpp
    cat > smoke.pro <<'EOF'
    QT += widgets network sql xml concurrent testlib
    CONFIG += console
    SOURCES = qt5-smoke.cpp
    TARGET = qt5-smoke
    EOF
    qmake smoke.pro
    runHook postConfigure
  '';
  enableParallelBuilding = true;
  doCheck = true;
  checkPhase = ''
    export QT_PLUGIN_PATH=${qt5.qtbase.bin}/${qt5.qtbase.qtPluginPrefix}
    export FONTCONFIG_FILE=${pkgs.makeFontsConf { fontDirectories = [ pkgs.dejavu_fonts ]; }}
    export HOME=$TMPDIR
    QT_QPA_PLATFORM=offscreen ./qt5-smoke
    QT_QPA_PLATFORM=xcb xvfb-run -a ./qt5-smoke
  '';
  installPhase = ''
    mkdir -p $out/bin
    cp qt5-smoke $out/bin/
  '';
}
