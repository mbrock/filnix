{ pkgs, pkgsFilc }:
pkgsFilc.glib-networking.overrideAttrs (old: {
  doCheck = true;
  postPatch = (old.postPatch or "") + ''
    # Fil-C's dlsym does not implement RTLD_NEXT. Resolve the real clock from
    # the already loaded Fil-C libc so the session-expiry tests can interpose it.
    substituteInPlace tls/tests/connection.c \
      --replace-fail 'dlsym (RTLD_NEXT,' 'dlsym (dlopen ("libc.so.6666", RTLD_LAZY),'
  '';
  preCheck = (old.preCheck or "") + ''
    export NIX_SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
  '';
})
