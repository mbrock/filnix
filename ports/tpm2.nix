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
        # Since 4.2 every test includes cmocka through this helper.
        substituteInPlace test/helper/cmocka_all.h \
          --replace-fail '#include <cmocka.h>' '#include "../cmocka-pointer-mocks.h"'
        substituteInPlace test/unit/esys-vendor.c \
          --replace-fail 'will_return_uint_always(tcti_fake_recv, (uintptr_t) __func__)' \
            'will_return_ptr_always(tcti_fake_recv, __func__)' \
          --replace-fail '(const char *)mock_type(uintptr_t)' 'mock_ptr_type(const char *)'
        # Preserve calls to the functions these tests interpose. The compiler
        # adapter restores their descriptor names after Fil-C's lowering.
        substituteInPlace Makefile-test.am \
          --replace-fail 'TESTS_CFLAGS = ' \
            'TESTS_CFLAGS = -Dmalloc=filnix_wrap_malloc -Dfree=filnix_wrap_free '
      '';
    }))
  ];
}
