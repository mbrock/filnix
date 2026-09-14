{ pkgs, pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-gi-link-environment-check";
  dontUnpack = true;
  nativeBuildInputs = [
    pkgs.pkg-config
    pkgsFilc.gobject-introspection
  ];
  buildInputs = [
    pkgsFilc.glib
    pkgsFilc.zlib
  ];
  buildPhase = ''
    cat > probe.h <<'HEADER'
    #include <glib-object.h>
    const char *filnix_probe_version(void);
    HEADER
    cat > probe.c <<'SOURCE'
    #include "probe.h"
    #include <zlib.h>
    const char *filnix_probe_version(void) { return zlibVersion(); }
    SOURCE
    $CC -shared -fPIC probe.c $(pkg-config --cflags --libs gobject-2.0 zlib) -o libfilnix-probe.so
    GI_SCANNER_DISABLE_CACHE=1 g-ir-scanner --namespace=Filnix --nsversion=1.0 \
      --identifier-prefix=Filnix --symbol-prefix=filnix \
      --include=GObject-2.0 --pkg=gobject-2.0 --pkg=zlib \
      --library=filnix-probe --library-path="$PWD" \
      --library-path=${pkgsFilc.zlib}/lib --output=Filnix-1.0.gir probe.h probe.c
    g-ir-compiler Filnix-1.0.gir -o Filnix-1.0.typelib
    test -s Filnix-1.0.typelib
  '';
  installPhase = ''
    mkdir "$out"
    cp Filnix-1.0.gir Filnix-1.0.typelib "$out/"
  '';
}
