# Exercise the installed CMake target, including its transitive math dependency.
{
  source ? ../.,
}:
let
  pkgs =
    (builtins.getFlake (toString source)).legacyPackages.x86_64-linux.pkgsFilc;
in
pkgs.stdenv.mkDerivation {
  pname = "quadprogpp-consumer-check";
  version = "1";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.buildPackages.cmake ];
  buildInputs = [ pkgs.QuadProgpp ];
  preConfigure = ''
    cp ${./quadprogpp.cc} main.cc
    cat > CMakeLists.txt <<'EOF'
    cmake_minimum_required(VERSION 3.16)
    project(quadprogpp_consumer CXX)
    include("${pkgs.QuadProgpp}/cmake/quadprog-targets.cmake")
    add_executable(consumer main.cc)
    target_link_libraries(consumer PRIVATE quadprog)
    enable_testing()
    add_test(NAME quadratic_solution COMMAND consumer)
    EOF
  '';
  doCheck = true;
  installPhase = ''
    runHook preInstall
    mkdir -p "$out/bin"
    cp consumer "$out/bin/quadprogpp-consumer-check"
    runHook postInstall
  '';
}
