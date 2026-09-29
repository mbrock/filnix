# Focused repairs for shared graphics and codec dependencies.
{ pkgs }:
let
  inherit (import ./. { inherit (pkgs) lib pkgs; })
    for
    patch
    addMesonFlag
    configure
    use
    ;
in
{
  coin3d = for pkgs.coin3d [
    (patch ../patches/coin-link-math.patch)
    (patch ../patches/coin-external-fields.patch)
    (use { doCheck = true; })
  ];
  fltk14 = for pkgs.fltk14 [ (patch ../patches/fltk14-link-math.patch) ];
  mesa_glu = for pkgs.mesa_glu [
    (patch ../patches/glu-link-math.patch)
  ];
  flac = for pkgs.flac [
    (patch ../patches/flac-xgetbv.patch)
    (patch ../patches/flac-zeroupper.patch)
  ];
  dav1d = for pkgs.dav1d [
    # NASM output has the native ABI. Use the upstream portable C decoder.
    (addMesonFlag "-Denable_asm=false")
  ];
  libvmaf = for pkgs.libvmaf [
    (addMesonFlag "-Denable_asm=false")
    (use { doCheck = true; })
  ];
  libdeflate = for pkgs.libdeflate [
    (patch ../patches/libdeflate-xgetbv.patch)
  ];
  timidity = for pkgs.timidity [
    # The old ALSA 0.9 API needs symbol versions the Fil-C alsa-lib lacks.
    (patch ../patches/timidity-alsa-new-api.patch)
    (patch ../patches/timidity-ctl-event-pointers.patch)
  ];
  mpg123 = for pkgs.mpg123 [
    # Keep the decoder API; select upstream's C implementation of its kernels.
    (configure "--with-cpu=generic")
    (use { doCheck = true; })
  ];
}
