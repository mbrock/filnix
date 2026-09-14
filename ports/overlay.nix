# Overlay for Fil-C ported packages
# Converts the port list from ../ports.nix into a nixpkgs overlay

pkgs: final: prev:
let
  portDSL = import ./default.nix { inherit (pkgs) lib pkgs; };
  portList = import ../ports.nix { inherit pkgs prev final; };
in
portDSL.makeOverlay portList final prev
// pkgs.lib.optionalAttrs prev.stdenv.hostPlatform.isFilc {
  # The scanner executes C dumpers and loads a Python C extension; GLib's
  # gdbus-codegen emits GType operations. Both must match the target GLib ABI
  # even though they run during builds. Explicit scope overrides still win,
  # and the native package set keeps its ordinary tools.
  newScope =
    extra:
    prev.newScope (
      {
        gobject-introspection = final.gobject-introspection;
        glib = final.glib;
      }
      // extra
    );
}
