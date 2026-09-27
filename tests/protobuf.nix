# Generate C++ with the Fil-C protoc and round-trip messages through the
# Fil-C runtime: binary, text and JSON formats, a JSON error (a heap-backed
# absl::Status), and a million-field message that must parse without a stack
# frame per field.
{
  pkgs,
  pkgsFilc,
  protobuf ? pkgsFilc.protobuf,
}:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-protobuf-${protobuf.version}-consumer-check";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.pkg-config ];
  buildInputs = [ protobuf ];
  buildPhase = ''
    cp ${./protobuf.proto} protobuf.proto
    ${protobuf}/bin/protoc --version
    ${protobuf}/bin/protoc --cpp_out=. protobuf.proto
    $CXX -std=c++17 -O2 ${./protobuf.cpp} protobuf.pb.cc -I. \
      $(pkg-config --cflags --libs protobuf) -o check
    ./check | tee check.log
    grep -q '^ok: ' check.log
  '';
  installPhase = ''
    touch "$out"
  '';
}
