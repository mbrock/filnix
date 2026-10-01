# QtBase/Svg and QML/Quick/Controls 2 runtime coverage, with native host tools.
# Run on both offscreen and X11 platforms using Quick's software renderer.
{
  source ? ../.,
}:
let
  pkgs =
    (builtins.getFlake (toString source)).legacyPackages.x86_64-linux.pkgsFilc;
  qt6 = pkgs.pkgsHostTarget.qt6;
in
pkgs.stdenv.mkDerivation {
  pname = "qt6-smoke-check";
  version = "1";
  dontUnpack = true;
  dontWrapQtApps = true;
  nativeBuildInputs = [
    pkgs.pkgsBuildBuild.cmake
    pkgs.pkgsBuildBuild.ninja
    pkgs.pkgsBuildBuild.xvfb-run
  ];
  buildInputs = [
    qt6.qtbase
    qt6.qtsvg
    qt6.qtdeclarative
  ];
  preConfigure = ''
    cp ${./qt5-smoke.cpp} qt5-smoke.cpp
    cp ${./qt6-contracts.cpp} qt6-contracts.cpp
    cp ${./qt5-contract-plugin.cpp} qt5-contract-plugin.cpp
    cp ${./qt6-qml.cpp} qt6-qml.cpp
    cp ${./qt6-quick.cpp} qt6-quick.cpp
    cp ${./qt6-hash.cpp} qt6-hash.cpp
    cat > CMakeLists.txt <<'EOF'
    cmake_minimum_required(VERSION 3.16)
    project(qt6-smoke LANGUAGES CXX)
    set(CMAKE_CXX_STANDARD 17)
    set(CMAKE_AUTOMOC ON)
    find_package(Qt6 REQUIRED COMPONENTS CorePrivate Widgets Network Sql Xml Concurrent Test Svg Qml QmlPrivate Quick QuickControls2)
    add_executable(qt6-smoke qt5-smoke.cpp)
    target_link_libraries(qt6-smoke PRIVATE Qt6::Widgets Qt6::Network Qt6::Sql Qt6::Xml Qt6::Concurrent Qt6::Test)
    add_executable(qt6-contracts qt6-contracts.cpp)
    target_link_libraries(qt6-contracts PRIVATE Qt6::Core Qt6::Gui Qt6::Svg)
    add_library(qt6-contract-plugin MODULE qt5-contract-plugin.cpp)
    target_link_libraries(qt6-contract-plugin PRIVATE Qt6::Core)
    add_executable(qt6-qml qt6-qml.cpp)
    target_link_libraries(qt6-qml PRIVATE Qt6::QmlPrivate)
    add_executable(qt6-quick qt6-quick.cpp)
    target_link_libraries(qt6-quick PRIVATE Qt6::Qml Qt6::Quick Qt6::QuickControls2 Qt6::Test)
    add_executable(qt6-hash qt6-hash.cpp)
    target_link_libraries(qt6-hash PRIVATE Qt6::CorePrivate)
    install(TARGETS qt6-smoke qt6-contracts qt6-contract-plugin qt6-qml qt6-quick qt6-hash DESTINATION bin)
    EOF
  '';
  cmakeFlags = [
    "-DQT_HOST_PATH=${pkgs.pkgsBuildBuild.qt6.qtbase}"
    "-DQt6QmlTools_DIR=${pkgs.pkgsBuildBuild.qt6.qtdeclarative}/lib/cmake/Qt6QmlTools"
    "-DQt6QuickTools_DIR=${pkgs.pkgsBuildBuild.qt6.qtdeclarative}/lib/cmake/Qt6QuickTools"
  ];
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    export QT_PLUGIN_PATH=${qt6.qtbase}/${qt6.qtbase.qtPluginPrefix}:${qt6.qtsvg}/${qt6.qtbase.qtPluginPrefix}:${qt6.qtdeclarative}/${qt6.qtbase.qtPluginPrefix}
    export QML_IMPORT_PATH=${qt6.qtdeclarative}/${qt6.qtbase.qtQmlPrefix}
    export QT_QUICK_BACKEND=software
    export QT_QUICK_CONTROLS_STYLE=Basic
    export FONTCONFIG_FILE=${
      pkgs.makeFontsConf { fontDirectories = [ pkgs.pkgsBuildBuild.dejavu_fonts ]; }
    }
    export HOME=$TMPDIR
    QT_HASH_SEED=0 ./qt6-hash
    ./qt6-contracts "$PWD/libqt6-contract-plugin.so"
    ./qt6-qml
    QT_QPA_PLATFORM=offscreen ./qt6-smoke
    QT_QPA_PLATFORM=offscreen ./qt6-quick
    QT_QPA_PLATFORM=xcb FILNIX_QT_SCREENSHOT="$PWD/qt6-xcb.png" \
      xvfb-run -a -s "-screen 0 640x480x24" ./qt6-smoke
    QT_QPA_PLATFORM=xcb FILNIX_QT_QUICK_SCREENSHOT="$PWD/qt6-quick-xcb.png" \
      xvfb-run -a -s "-screen 0 640x480x24" ./qt6-quick
    runHook postCheck
  '';
  postInstall = ''
    mkdir -p "$out/share/qt6-smoke"
    cp qt6-xcb.png qt6-quick-xcb.png qt6-quick-xcb.png.popup.png "$out/share/qt6-smoke/"
  '';
}
