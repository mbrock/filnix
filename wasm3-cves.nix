# CVE test payloads for wasm3
{ pkgs }:

let
  # Fetch CVE exploit files
  cve-2022-39974-gz = pkgs.fetchurl {
    url = "https://github.com/wasm3/wasm3/files/9441091/op_Select_i32_srs.wasm.gz";
    sha256 = "sha256-i9IoHMfkIvX210bTI6rhjICJCszk+8qu6yxeTUlOTdg=";
  };

  cve-2022-34529-zip = pkgs.fetchurl {
    url = "https://github.com/wasm3/wasm3/files/8939432/poc.wasm.zip";
    sha256 = "sha256-L53OS5YiySPa0wZEqJxX1ineFw1XS4mvTEqglsdkNX0=";
  };

  cve-tests = pkgs.runCommand "wasm3-cve-tests" {
    nativeBuildInputs = [ pkgs.gzip pkgs.unzip ];
  } ''
    mkdir -p $out
    gunzip -c ${cve-2022-39974-gz} > $out/cve-2022-39974.wasm
    unzip -p ${cve-2022-34529-zip} poc.wasm > $out/cve-2022-34529.wasm
  '';

in {
  inherit cve-tests;
}
