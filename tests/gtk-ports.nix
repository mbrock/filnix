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
