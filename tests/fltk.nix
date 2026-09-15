# Exercise installed CMake targets, including their transitive link dependencies.
{
  source ? ../.,
}:
let
  pkgs =
    (builtins.getFlake (toString source)).legacyPackages.x86_64-linux.pkgsFilc;
in
pkgs.stdenv.mkDerivation {
  pname = "fltk-consumer-check";
  version = "1";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.buildPackages.cmake ];
  buildInputs = [ pkgs.fltk14 ];
  configurePhase = ''
    runHook preConfigure
    cp ${./fltk-consumer.cxx} consumer.cxx
    cat > CMakeLists.txt <<'EOF'
    cmake_minimum_required(VERSION 3.16)
    project(FltkConsumer CXX)
    find_package(FLTK CONFIG REQUIRED)
    foreach(kind IN ITEMS static shared)
      add_executable(consumer-''${kind} consumer.cxx)
      target_include_directories(consumer-''${kind} PRIVATE ''${FLTK_INCLUDE_DIRS})
    endforeach()
    # This package enables FLTK's Cairo extension; consumers opt into its
    # companion library, as they do with fltk-config --use-cairo.
    target_link_libraries(consumer-static PRIVATE fltk fltk_cairo fltk)
    target_link_libraries(consumer-shared PRIVATE fltk_cairo_SHARED)
    EOF
    cmake -S . -B build -DFLTK_DIR=${pkgs.fltk14}/share/fltk
    runHook postConfigure
  '';
  buildPhase = ''
    cmake --build build --parallel "$NIX_BUILD_CORES"
  '';
  doCheck = true;
  checkPhase = ''
    ./build/consumer-static
    ./build/consumer-shared
  '';
  installPhase = ''
    mkdir -p "$out/bin"
    cp build/consumer-* "$out/bin/"
  '';
}
