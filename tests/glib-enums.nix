{ pkgs, pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-meson-gtype-check";
  src = ./glib-enums;
  nativeBuildInputs = [
    (import ../toolchain/meson-filc.nix { inherit pkgs; })
    pkgs.ninja
    pkgs.pkg-config
    # Unspliced: Fil-C's glib-mkenums, not the build platform's.
    (removeAttrs pkgsFilc.glib [ "__spliced" ])
  ];
  buildInputs = [ pkgsFilc.glib ];
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    ./gtype-enums-check
    runHook postCheck
  '';
}
