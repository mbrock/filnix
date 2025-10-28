{ stdenv, lib, fetchgit, cmake, ninja }:

stdenv.mkDerivation {
  pname = "wasm3";
  version = "0.5.1";

  src = fetchgit {
    url = "https://github.com/wasm3/wasm3";
    rev = "79d412ea5fcf92f0efe658d52827a0e0a96ff442";
    hash = "sha256-CmNngYLD/PtiEW8pGORjW4d7TAmW5ZZMBAeKzjYMMdw=";
  };

  enableParallelBuilding = true;

  nativeBuildInputs = [ cmake ninja ];

  cmakeFlags = [
    "-DBUILD_WASI=simple"
  ];

  meta = with lib; {
    homepage = "https://github.com/wasm3/wasm3";
    description = "Fast WebAssembly interpreter";
    license = licenses.mit;
  };
}
