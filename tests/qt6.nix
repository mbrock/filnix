# QtBase runtime coverage using the same fixture as Qt 5, built with CMake
# and the native Qt 6 moc. Run on both offscreen and X11 platforms.
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
  ];
  preConfigure = ''
    cp ${./qt5-smoke.cpp} qt5-smoke.cpp
    cp ${./qt6-contracts.cpp} qt6-contracts.cpp
    cp ${./qt5-contract-plugin.cpp} qt5-contract-plugin.cpp
    cat > CMakeLists.txt <<'EOF'
    cmake_minimum_required(VERSION 3.16)
    project(qt6-smoke LANGUAGES CXX)
    set(CMAKE_CXX_STANDARD 17)
    set(CMAKE_AUTOMOC ON)
    find_package(Qt6 REQUIRED COMPONENTS Widgets Network Sql Xml Concurrent Test Svg)
    add_executable(qt6-smoke qt5-smoke.cpp)
    target_link_libraries(qt6-smoke PRIVATE Qt6::Widgets Qt6::Network Qt6::Sql Qt6::Xml Qt6::Concurrent Qt6::Test)
    add_executable(qt6-contracts qt6-contracts.cpp)
    target_link_libraries(qt6-contracts PRIVATE Qt6::Core Qt6::Gui Qt6::Svg)
    add_library(qt6-contract-plugin MODULE qt5-contract-plugin.cpp)
    target_link_libraries(qt6-contract-plugin PRIVATE Qt6::Core)
    install(TARGETS qt6-smoke qt6-contracts qt6-contract-plugin DESTINATION bin)
    EOF
  '';
  cmakeFlags = [
    "-DQT_HOST_PATH=${pkgs.pkgsBuildBuild.qt6.qtbase}"
  ];
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    export QT_PLUGIN_PATH=${qt6.qtbase}/${qt6.qtbase.qtPluginPrefix}
    export FONTCONFIG_FILE=${
      pkgs.makeFontsConf { fontDirectories = [ pkgs.pkgsBuildBuild.dejavu_fonts ]; }
    }
    export HOME=$TMPDIR
    ./qt6-contracts "$PWD/libqt6-contract-plugin.so"
    QT_QPA_PLATFORM=offscreen ./qt6-smoke
    QT_QPA_PLATFORM=xcb FILNIX_QT_SCREENSHOT="$PWD/qt6-xcb.png" \
      xvfb-run -a -s "-screen 0 640x480x24" ./qt6-smoke
    runHook postCheck
  '';
  postInstall = ''
    mkdir -p "$out/share/qt6-smoke"
    cp qt6-xcb.png "$out/share/qt6-smoke/"
  '';
}
