# dbus-glib consumer check: a Fil-C service and client exchange scalars,
# containers, a struct, a variant dictionary and a signal through
# dbus-binding-tool glue, as an ordinary spliced consumer builds it.
{ pkgs, pkgsFilc }:
pkgsFilc.callPackage (
  {
    stdenv,
    pkg-config,
    dbus-glib,
  }:
  stdenv.mkDerivation {
    name = "filc-dbus-glib-check";
    src = ./dbus-glib;
    nativeBuildInputs = [
      pkg-config
      dbus-glib
    ];
    buildInputs = [ dbus-glib ];
    buildPhase = ''
      dbus-binding-tool --mode=glib-server --prefix=probe probe.xml > probe-server.h
      dbus-binding-tool --mode=glib-client probe.xml > probe-client.h
      flags=$($PKG_CONFIG --cflags --libs dbus-glib-1 gobject-2.0)
      $CC -Wno-deprecated-declarations service.c $flags -o service
      $CC -Wno-deprecated-declarations client.c $flags -o client

      export HOME=$TMPDIR
      ${pkgs.dbus}/bin/dbus-run-session --config-file=${pkgs.dbus}/share/dbus-1/session.conf -- bash -euc '
        ./service &
        for _ in $(seq 100); do
          ${pkgs.dbus}/bin/dbus-send --session --print-reply \
            --dest=org.freedesktop.DBus / org.freedesktop.DBus.NameHasOwner \
            string:org.filnix.Probe | grep -q "boolean true" && break
          sleep 0.1
        done
        ./client > actual
        kill %1
      '
      diff -u expected actual
    '';
    installPhase = ''
      mkdir "$out"
      cp probe-server.h probe-client.h actual "$out/"
    '';
  }
) { }
