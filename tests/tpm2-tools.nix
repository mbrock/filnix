# Exercise the installed Fil-C tools and broker against an isolated software TPM.
{
  source ? ../.,
}:
let
  filc =
    (builtins.getFlake (toString source)).legacyPackages.x86_64-linux.pkgsFilc;
  pkgs = filc.buildPackages.buildPackages;
in
pkgs.runCommand "filc-tpm2-tools-check"
  {
    nativeBuildInputs = [
      pkgs.swtpm
      pkgs.dbus
      filc.tpm2-tools
      filc.tpm2-abrmd
    ];
  }
  ''
    timeout 90 dbus-run-session \
      --config-file=${pkgs.dbus}/share/dbus-1/session.conf \
      -- ${pkgs.bash}/bin/bash ${./tpm2-tools.sh}
    mkdir "$out"
    cp *.log digest.bin public.pem "$out/"
  ''
