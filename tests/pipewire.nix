{
  pkgs,
  pkgsFilc,
  filcc,
}:
let
  core = import ../packages/pipewire-core.nix {
    native = pkgs;
    p = pkgsFilc;
  };
in
{
  inherit core;
  runtime = pkgs.runCommand "pipewire-shared-libc-runtime-check" { } ''
    ${pkgs.python3}/bin/python ${./pipewire-runtime.py} \
      --pipewire ${core} --libc ${filcc.filc-glibc} > "$out"
  '';
}
