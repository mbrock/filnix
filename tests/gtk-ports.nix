# Evaluate with --option allow-import-from-derivation false; builds nothing.
# Check the ABI boundary: Fil-C builds splice in build-platform generators
# that are patched for their Fil-C target.
let
  flake = builtins.getFlake (toString ../.);
  pkgs = import flake.inputs.nixpkgs { system = "x86_64-linux"; };
  inherit (pkgs) lib;
  ports = flake.legacyPackages.x86_64-linux.pkgsFilc;
  build = ports.buildPackages;
  gi = ports.gobject-introspection-unwrapped;
  python = ports.python3.withPackages (ps: [
    ps.mako
    ps.markdown
    ps.setuptools
  ]);
  containsDrv =
    expected: inputs:
    builtins.any (input: (input.drvPath or null) == expected.drvPath) inputs;
  # nativeBuildInputs as mkDerivation resolved them, after splicing.
  usesTool =
    tool: pkg:
    builtins.elem (lib.getDev tool).outPath (
      map (input: input.outPath or (toString input)) pkg.drvAttrs.nativeBuildInputs
    );
  hasPatch =
    name: pkg:
    builtins.any (patch: lib.hasSuffix name (toString patch)) pkg.patches;
  gtkScanner =
    gtk:
    assert usesTool build.gobject-introspection gtk;
    assert !(usesTool pkgs.gobject-introspection gtk);
    gtk.drvPath;
in
assert hasPatch "glib-filc-generators.patch" build.glib;
assert hasPatch "gobject-introspection-filc-scanner.patch"
  build.gobject-introspection-unwrapped;
assert hasPatch "meson-gtype.patch" build.meson;
# Generators must not emit APIs newer than the target GLib and GI provide.
assert build.glib.version == ports.glib.version;
assert build.gobject-introspection-unwrapped.version == gi.version;
assert !(hasPatch "glib-filc-generators.patch" pkgs.glib);
assert !(hasPatch "meson-gtype.patch" pkgs.meson);
assert usesTool build.glib ports.gtk3;
assert usesTool build.meson ports.gtk4;
assert containsDrv python gi.buildInputs;
assert builtins.elem "-Dpython=${python}/bin/python3" gi.mesonFlags;
assert builtins.elem "-Dgi_cross_use_prebuilt_gi=false" gi.mesonFlags;
assert !(builtins.elem "-Dgi_cross_use_prebuilt_gi=true" gi.mesonFlags);
assert
  !(containsDrv pkgs.gobject-introspection-unwrapped gi.nativeBuildInputs);
assert !(containsDrv gi gi.nativeBuildInputs);
assert builtins.all (
  input: !(pkgs.lib.hasPrefix "gobject-introspection" (input.pname or ""))
) ports.glib.nativeBuildInputs;
assert gi.version == "1.80.1";
assert ports.gtk3.version == "3.24.52";
assert ports.gtk4.version == "4.14.5";
assert builtins.elem "-Dintrospection=true" ports.gtk3.mesonFlags;
assert builtins.elem "-Dintrospection=enabled" ports.gtk4.mesonFlags;
assert builtins.elem "-Dmedia-gstreamer=disabled" ports.gtk4.mesonFlags;
assert builtins.all (
  input:
  !(builtins.elem (input.pname or "") [
    "gst-plugins-base"
    "gst-plugins-bad"
  ])
) ports.gtk4.buildInputs;
assert containsDrv ports.systemdLibs ports.at-spi2-core.buildInputs;
assert !(containsDrv ports.systemd ports.at-spi2-core.buildInputs);
assert builtins.all (usesTool build.gobject-introspection) [
  ports.pango
  ports.harfbuzz
  ports.gdk-pixbuf
  ports.graphene
  ports.at-spi2-core
];
# Unported packages splice in the same generators.
assert usesTool build.gobject-introspection ports.libproxy;
assert usesTool build.gobject-introspection ports.python3Packages.pygobject3;
assert usesTool build.glib ports.dconf;
assert !(containsDrv ports.vala ports.dconf.buildInputs);
assert ports.python3Packages.pygobject3.version == "3.48.2";
assert
  (pkgs.callPackage ({ gobject-introspection }: gobject-introspection) { })
  .drvPath == pkgs.gobject-introspection.drvPath;
# Keep the pinned Nixpkgs release and its security fixes when adding the port.
assert ports.gnutls.version == pkgs.gnutls.version;
assert builtins.all (
  patch: builtins.elem patch ports.gnutls.patches
) pkgs.gnutls.patches;
{
  gtk3 = gtkScanner ports.gtk3;
  gtk4 = gtkScanner ports.gtk4;
  gnutls = ports.gnutls.drvPath;
  introspection = gi.drvPath;
  compiler = flake.packages.x86_64-linux.filcc.drvPath;
}
