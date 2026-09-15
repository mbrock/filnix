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
  mpg123 = for pkgs.mpg123 [
    # Keep the decoder API; select upstream's C implementation of its kernels.
    (configure "--with-cpu=generic")
    (use { doCheck = true; })
  ];
}
