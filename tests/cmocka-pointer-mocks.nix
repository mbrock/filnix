{
  source ? ../.,
}:
let
  pkgs =
    (builtins.getFlake (toString source)).legacyPackages.x86_64-linux.pkgsFilc;
  cmocka = builtins.head (
    builtins.filter (p: (p.pname or "") == "cmocka") pkgs.tpm2-tss.buildInputs
  );
in
pkgs.stdenv.mkDerivation {
  pname = "filc-cmocka-pointer-mocks-check";
  version = "1";
  dontUnpack = true;
  buildInputs = [ cmocka ];
  buildPhase = ''
    $CC -I${../toolchain} ${./cmocka-pointer-mocks.c} -lcmocka -o check-mocks
  '';
  doCheck = true;
  checkPhase = "./check-mocks";
  installPhase = ''
    mkdir -p "$out/bin"
    cp check-mocks "$out/bin/"
  '';
}
