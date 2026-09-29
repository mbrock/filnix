# Focused repairs for shared graphics and codec dependencies.
{ pkgs }:
let
  inherit (import ./. { inherit (pkgs) lib pkgs; })
    for
    patch
    addMesonFlag
    addMakeFlag
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
  p7zip = for pkgs.p7zip [
    # makefile.machine says gcc and g++. Nixpkgs prepends the target
    # prefix when cross-compiling, but Fil-C's is empty, leaving gcc.
    (addMakeFlag "CC=clang")
    (addMakeFlag "CXX=clang++")
    (patch ../patches/p7zip-hash-stdint.patch)
    (patch ../patches/p7zip-zstd-p2align.patch)
    (use {
      doCheck = true;
      # test_7z also checks RAR archives, whose codec the free source drops.
      checkTarget = "test test_7zr";
    })
  ];
  libmhash = for pkgs.libmhash [
    # AC_FUNC_MALLOC cannot run its probe when cross-compiling, assumes
    # malloc(0) returns NULL and renames malloc to an rpl_malloc that
    # mhash does not provide. glibc's malloc(0) returns a pointer.
    (configure "ac_cv_func_malloc_0_nonnull=yes")
    (patch ../patches/mhash-test-use-after-free.patch)
    (use {
      doCheck = true;
      # hash_test.sh generates the million-"a" SHA-1 input with perl.
      nativeCheckInputs = [ pkgs.perl ];
    })
  ];
  mpg123 = for pkgs.mpg123 [
    # Keep the decoder API; select upstream's C implementation of its kernels.
    (configure "--with-cpu=generic")
    (use { doCheck = true; })
  ];
}
