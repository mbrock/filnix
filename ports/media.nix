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
  tpm2-tss = for pkgs.tpm2-tss [
    (use (import ../toolchain/test-wrap.nix { inherit pkgs; }))
    (patch ../patches/tpm2-test-environment.patch)
  ];
  coin3d = for pkgs.coin3d [
    (patch ../patches/coin-link-math.patch)
    (patch ../patches/coin-external-fields.patch)
    (patch ../patches/coin-test-stack.patch)
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
  mpg123 = for pkgs.mpg123 [
    # Keep the decoder API; select upstream's C implementation of its kernels.
    (configure "--with-cpu=generic")
    (use { doCheck = true; })
  ];
}
