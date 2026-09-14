{ pkgs, pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-media-foundations-check";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.pkg-config ];
  buildInputs = [ pkgsFilc.alsa-lib ];
  buildPhase = ''
    $CC -Werror ${./alsa.c} $(pkg-config --cflags --libs alsa) -o alsa-check
    FUGC_THREADS=2 timeout 30 ./alsa-check
    PYTHONPATH=${pkgsFilc.libapparmor}/${pkgsFilc.python3.sitePackages} \
      ${pkgsFilc.python3}/bin/python3 -c \
      'import LibAppArmor; assert LibAppArmor.aa_splitcon("example (enforce)") == ["example", "enforce"]'
    ${pkgsFilc.systemdMinimal}/lib/systemd/systemd --version
    ${pkgsFilc.systemdMinimal}/bin/udevadm --version
    test "$(${pkgsFilc.systemdMinimal}/bin/systemd-escape --path /foo/bar)" = foo-bar
  '';
  installPhase = ''touch "$out"'';
}
