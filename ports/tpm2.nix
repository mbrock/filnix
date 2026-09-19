# TPM2's mocks must retain pointers, including Fil-C capabilities.
{ pkgs, final }:
let
  inherit (import ./. { inherit (pkgs) lib pkgs; })
    for
    arg
    use
    patch
    ;
  cmocka = final.cmocka.overrideAttrs (old: {
    version = "2.0.2";
    src = pkgs.fetchurl {
      url = "https://cmocka.org/files/2.0/cmocka-2.0.2.tar.xz";
      hash = "sha256-OfkvNmvfPxoCr02nW0pcUt9sn35zbH1l3hMoP58O9BY=";
    };
    # The old uintptr_t compatibility patch is no longer needed in 2.x.
    patches = [ ../patches/cmocka-filc-signal-test.patch ];
    doCheck = true;
  });
in
{
  tpm2-abrmd = for pkgs.tpm2-abrmd [
    (patch ../patches/tpm2-abrmd-gtype.patch)
  ];
  tpm2-tss = for pkgs.tpm2-tss [
    (arg { inherit cmocka; })
    (use (import ../toolchain/test-wrap.nix { inherit pkgs; }))
    (patch ../patches/tpm2-test-environment.patch)
    (patch ../patches/tpm2-spi-pointers.patch)
    (use (old: {
      postPatch = (old.postPatch or "") + ''
        cp ${../toolchain/cmocka-pointer-mocks.h} test/cmocka-pointer-mocks.h
        substituteInPlace test/unit/*.c test/integration/*.c \
          --replace-quiet '#include <cmocka.h>' '#include "../cmocka-pointer-mocks.h"'
        substituteInPlace test/unit/esys-vendor.c \
          --replace-fail '(const char*)(size_t)mock()' 'mock_ptr_type(const char *)'
        substituteInPlace test/unit/tcti-libtpms.c \
          --replace-fail 'check_expected_ptr(st)' 'check_expected(st)' \
          --replace-fail 'check_expected_ptr(buf_len)' 'check_expected(buf_len)'
        # Preserve calls to the functions these tests interpose. The compiler
        # adapter restores their descriptor names after Fil-C's lowering.
        substituteInPlace Makefile-test.am \
          --replace-fail 'TESTS_CFLAGS = ' \
            'TESTS_CFLAGS = -Dmalloc=filnix_wrap_malloc -Dfree=filnix_wrap_free '
      '';
    }))
  ];
}
