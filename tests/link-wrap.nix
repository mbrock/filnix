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
      $CC -Dmalloc=filnix_wrap_malloc -Dfree=filnix_wrap_free \
        -c ${./link-wrap.c} -o wrapped.o
      $CC -c ${./link-wrap-provider.c} -o provider.o
      flags='-Wl,--wrap=write,--wrap=calloc,--wrap=malloc,--wrap=wrapped_value'
      $CC wrapped.o provider.o $flags -o wrapped
      $CC provider.o wrapped.o $flags -o reversed
    '';
    doCheck = true;
    checkPhase = ''
      ./wrapped
      ./reversed
    '';
    installPhase = ''
      mkdir -p "$out/bin"
      cp wrapped "$out/bin/"
    '';
  }
)
