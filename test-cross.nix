# Test Fil-C cross-compilation with various packages
let
  filnix = builtins.getFlake "git+file:///home/mbrock/filnix";
  nixpkgs-filc = filnix.inputs.nixpkgs-filc;

  pkgs = import nixpkgs-filc {
    localSystem = { system = "x86_64-linux"; };
    crossSystem = { config = "x86_64-unknown-linux-filc"; };
    config.replaceCrossStdenv = { buildPackages, baseStdenv }: filnix.packages.x86_64-linux.filenv;
    # Use pre-built packages from filnix ports instead of rebuilding
    overlays = [
      (final: prev: filnix.packages.x86_64-linux.ports)
    ];
  };
in
{
  # Simple programs
  hello = pkgs.hello;
  coreutils = pkgs.coreutils;

  # Libraries
  zlib = pkgs.zlib;
  openssl = pkgs.openssl;

  # Utilities with dependencies
  curl = pkgs.curl;
  jq = pkgs.jq;

  lynx = pkgs.lynx;

  # Check symbols in a built binary
  checkHello = pkgs.runCommand "check-hello" {} ''
    echo "=== LDD output ===" > $out
    ldd ${pkgs.hello}/bin/hello >> $out
    echo "" >> $out
    echo "=== Pizlonated symbols ===" >> $out
    nm ${pkgs.hello}/bin/hello | grep pizlonated | head -10 >> $out
  '';
}
