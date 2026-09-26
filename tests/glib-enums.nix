{ pkgs, pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-meson-gtype-check";
  src = ./glib-enums;
  nativeBuildInputs = [
    pkgsFilc.meson
    pkgs.ninja
    pkgs.pkg-config
    pkgsFilc.glib
  ];
  buildInputs = [ pkgsFilc.glib ];
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    ./gtype-enums-check
    runHook postCheck
  '';
}
