{ callPackage, fetchurl }:
(callPackage ./openssl.nix { withSafeAssembly = true; }).overrideAttrs (old: {
  pname = "openssl-sarcasm";
  version = "3.6.5";
  src = fetchurl {
    url = "https://github.com/openssl/openssl/releases/download/openssl-3.6.5/openssl-3.6.5.tar.gz";
    hash = "sha256-ohV8KDDv3sN4iTmwDJsGODBtPwu7dtxIMu5QO7OX35g=";
  };
  # Keep openssl.nix's NIX_SSL_CERT_FILE patch; Nixpkgs uses it for 3.6 too.
  patches = [
    ./patch/openssl-sarcasm-3.6.5.patch
  ]
  ++ builtins.tail old.patches;
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
