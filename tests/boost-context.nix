{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-boost-context-check";
  dontUnpack = true;
  buildInputs = [ pkgsFilc.boost187 ];
  buildPhase = ''
    $CXX -std=c++17 ${./boost-context.cpp} -lboost_context -lboost_json -pthread -o check
    ./check
    $CXX -std=c++17 ${./boost-continuation.cpp} -lboost_context -pthread -o continuation-check
    ./continuation-check
  '';
  installPhase = ''touch "$out"'';
}
