{ callPackage, fetchurl }:
(callPackage ./openssl.nix { withSafeAssembly = true; }).overrideAttrs (old: {
  pname = "openssl-sarcasm";
  version = "3.6.4";
  src = fetchurl {
    url = "https://www.openssl.org/source/openssl-3.6.4.tar.gz";
    hash = "sha256-m/+qGtHgezVMIb0zJOwC+hVXn0Wn0ElLPnS8RJtzM+8=";
  };
  patches = [ ./patch/openssl-3.6.4.patch ];
  # The upstream perlasm generators emit Fil-C annotations with this enabled.
  # clang's default assembler is SaRCAsm; never use -yolo-assembler here.
  SARCASM = "1";
  configureFlags = old.configureFlags ++ [ "no-padlockeng" ];
  doCheck = true;
  preCheck = "patchShebangs util test";
  checkPhase = ''
    runHook preCheck
    HARNESS_JOBS=$NIX_BUILD_CORES make test
    runHook postCheck
  '';
  meta = old.meta // {
    description = "OpenSSL with memory-safe assembly through Fil-C and SaRCAsm";
  };
})
