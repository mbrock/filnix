{
  pkgs,
  pkgsFilc,
  filcc,
}:
{
  # Its build runs PipeWire's own test suites and the pointer-table check.
  inherit (pkgsFilc) pipewire;
  # The installed daemon with WirePlumber as its session manager: WirePlumber
  # links pw-cat's stream to a virtual sink, and wpctl lists the sink.
  runtime = pkgs.runCommand "pipewire-runtime-check" { } ''
    ${pkgs.python3}/bin/python ${./pipewire-runtime.py} \
      --pipewire ${pkgsFilc.pipewire} --libc ${filcc.filc-glibc} \
      --wireplumber ${pkgsFilc.wireplumber}/bin/wireplumber --play \
      --wpctl ${pkgsFilc.wireplumber}/bin/wpctl > "$out"
  '';
}
