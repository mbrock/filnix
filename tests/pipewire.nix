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
  # The consumer cohort's WirePlumber is built against the core profile.
  wireplumber = pkgsFilc.wireplumber.override { inherit (pkgsFilc) pipewire; };
in
{
  inherit core;
  runtime = pkgs.runCommand "pipewire-shared-libc-runtime-check" { } ''
    ${pkgs.python3}/bin/python ${./pipewire-runtime.py} \
      --pipewire ${core} --libc ${filcc.filc-glibc} > "$out"
  '';
  # The full Nixpkgs PipeWire with WirePlumber as its session manager:
  # WirePlumber links pw-cat's stream to the virtual sink, and wpctl lists it.
  full = pkgs.runCommand "pipewire-full-runtime-check" { } ''
    ${pkgs.python3}/bin/python ${./pipewire-runtime.py} \
      --pipewire ${pkgsFilc.pipewire} --libc ${filcc.filc-glibc} \
      --wireplumber ${wireplumber}/bin/wireplumber --play \
      --wpctl ${wireplumber}/bin/wpctl > "$out"
  '';
}
