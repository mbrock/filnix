# Run GnuTLS's TLS, certificate and slow suites separately from gnulib's
# allocator/stack/inline-assembly portability probes.
{ pkgs, pkgsFilc }:
pkgsFilc.gnutls.overrideAttrs (old: {
  doCheck = true;
  nativeCheckInputs = (old.nativeCheckInputs or [ ]) ++ [
    pkgs.which
    pkgs.nettools
    pkgs.util-linux
  ];
  postPatch = (old.postPatch or "") + ''
    # The upstream port fixes this same DSO argument in lib/atfork.c; the test
    # module has its own copy. All fifteen mock1 PKCS#11 tests reach it.
    substituteInPlace tests/pkcs11/pkcs11-mock.c \
      --replace-fail '__register_atfork(NULL, NULL, fork_handler, __dso_handle)' \
        '__register_atfork(NULL, NULL, fork_handler, NULL)'
    # Invalid API sequences deliberately trigger Nettle assertions. Fil-C's
    # abort traps with SIGTRAP rather than the native SIGABRT. Only the
    # invalid-API subtests may trap; happy-path traps remain failures.
    substituteInPlace tests/slow/cipher-api-test.c \
      --replace-fail 'check_status(int status)' 'check_status(int status, int may_trap)' \
      --replace-fail 'check_status(status);' \
        'check_status(status, func != test_cipher_happy && func != test_aead_happy);' \
      --replace-fail 'WTERMSIG(status) != SIGABRT' \
        '(!may_trap || (WTERMSIG(status) != SIGABRT && WTERMSIG(status) != SIGTRAP))'
  '';
  checkPhase = ''
    runHook preCheck
    if ! make -C tests -j"$NIX_BUILD_CORES" check; then
      find tests -name test-suite.log -exec cat {} \;
      exit 1
    fi
    runHook postCheck
  '';
})
