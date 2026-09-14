# Evaluate with --option allow-import-from-derivation false; builds nothing.
# Check the ABI boundary where Nix normally splices in native scanner tools.
let
  flake = builtins.getFlake (toString ../.);
  pkgs = import flake.inputs.nixpkgs { system = "x86_64-linux"; };
  ports = flake.legacyPackages.x86_64-linux.pkgsFilc;
  gi = ports.gobject-introspection-unwrapped;
  python = ports.python3.withPackages (ps: [
    ps.mako
    ps.markdown
    ps.setuptools
  ]);
  containsDrv =
    expected: inputs:
    builtins.any (input: (input.drvPath or null) == expected.drvPath) inputs;
  gtkScanner =
    gtk:
    assert containsDrv ports.gobject-introspection gtk.nativeBuildInputs;
    assert !(containsDrv pkgs.gobject-introspection gtk.nativeBuildInputs);
    gtk.drvPath;
in
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
assert builtins.all
  (pkg: containsDrv ports.gobject-introspection pkg.nativeBuildInputs)
  [
    ports.pango
    ports.harfbuzz
    ports.gdk-pixbuf
    ports.graphene
    ports.at-spi2-core
  ];
# Unported packages inherit ABI-matched generators from callPackage too.
assert containsDrv ports.gobject-introspection
  ports.libproxy.nativeBuildInputs;
assert containsDrv ports.gobject-introspection
  ports.python3Packages.pygobject3.nativeBuildInputs;
assert containsDrv ports.glib ports.dconf.nativeBuildInputs;
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
