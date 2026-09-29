# Native build tools propagate the ordinary GLib and GI into Fil-C builds
# (gdk-pixbuf, PyGObject). The twins' generators must still come first on
# PATH and in the build pkg-config path, where Meson finds gdbus-codegen.
{ pkgs, pkgsFilc }:
let
  build = pkgsFilc.buildPackages;
in
pkgsFilc.stdenv.mkDerivation {
  name = "filc-generator-precedence-check";
  dontUnpack = true;
  strictDeps = true;
  depsBuildBuild = [ pkgs.pkg-config ];
  nativeBuildInputs = [
    build.gdk-pixbuf
    build.python3Packages.pygobject3
    build.glib
    build.gobject-introspection
  ];
  buildPhase = ''
    test "$(command -v gdbus-codegen)" = ${build.glib.dev}/libexec/filc-generators/gdbus-codegen
    test "$(command -v g-ir-scanner)" = ${build.gobject-introspection.dev}/bin/g-ir-scanner
    export PKG_CONFIG_PATH=$PKG_CONFIG_PATH_FOR_BUILD
    test "$(pkg-config --variable=gdbus_codegen gio-2.0)" = ${build.glib.dev}/bin/gdbus-codegen
    test "$(pkg-config --modversion gobject-introspection-1.0)" = ${build.gobject-introspection.version}
  '';
  installPhase = "touch $out";
}
