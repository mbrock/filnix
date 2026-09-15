# Installed API checks, without a display server or target encoder dependency.
{
  source ? ../.,
}:
let
  pkgs =
    (builtins.getFlake (toString source)).legacyPackages.x86_64-linux.pkgsFilc;
in
pkgs.stdenv.mkDerivation {
  pname = "media-consumer-check";
  version = "1";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.buildPackages.pkg-config ];
  buildInputs = [
    pkgs.mesa_glu
    pkgs.dav1d
  ];
  buildPhase = ''
    runHook preBuild
    $CC ${./glu-consumer.c} $("$PKG_CONFIG" --cflags --libs glu) -o glu-consumer
    $CC ${./dav1d-consumer.c} $("$PKG_CONFIG" --cflags --libs dav1d) -o dav1d-consumer
    runHook postBuild
  '';
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    ./glu-consumer
    ./dav1d-consumer ${./fixtures/av1/gradient-8.obu} 8
    ./dav1d-consumer ${./fixtures/av1/gradient-10.obu} 10
    runHook postCheck
  '';
  installPhase = ''
    mkdir -p "$out/bin"
    cp glu-consumer dav1d-consumer "$out/bin/"
  '';
}
