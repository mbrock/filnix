{
  source ? ../.,
}:
let
  pkgs =
    (builtins.getFlake (toString source)).legacyPackages.x86_64-linux.pkgsFilc;
  adapter = import ../toolchain/test-wrap.nix {
    pkgs = pkgs.buildPackages.buildPackages;
  };
in
pkgs.stdenv.mkDerivation (
  (adapter { })
  // {
    pname = "filc-link-wrap-check";
    version = "1";
    dontUnpack = true;
    configurePhase = ''
      runHook preConfigure
      runHook postConfigure
    '';
    buildPhase = ''
      $CC -c ${./link-wrap.c} -o wrapped.o
      $CC wrapped.o -Wl,--wrap=write,--wrap=calloc -o wrapped
    '';
    doCheck = true;
    checkPhase = "./wrapped";
    installPhase = ''
      mkdir -p "$out/bin"
      cp wrapped "$out/bin/"
    '';
  }
)
