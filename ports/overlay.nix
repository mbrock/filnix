# Overlay for Fil-C ported packages
# Converts the port list from ../ports.nix into a nixpkgs overlay

pkgs: final: prev:
let
  portDSL = import ./default.nix { inherit (pkgs) lib pkgs; };
  portList = import ../ports.nix { inherit pkgs prev final; };
in
portDSL.makeOverlay portList final prev
// pkgs.lib.optionalAttrs prev.stdenv.hostPlatform.isFilc {
  gst_all_1 = prev.gst_all_1 // {
    # Only the optional PTP clock helper uses Rust. The multimedia core is C.
    gstreamer =
      (prev.gst_all_1.gstreamer.override {
        withRust = false;
        # Native stack unwinding does not understand Fil-C frames.
        withLibunwind = false;
      }).overrideAttrs
        (
          old:
          (import ../toolchain/meson-check-cores.nix { inherit pkgs; }) old
          // {
            patches = (old.patches or [ ]) ++ [
              ./patch/gstreamer-1.24.7.patch
              ../patches/gstreamer-execinfo.patch
            ];
            doCheck = true;
            env = (old.env or { }) // {
              CK_TIMEOUT_MULTIPLIER = "5";
            };
          }
        );
  };

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
        # mkenums_simple embeds C templates independently of glib-mkenums.
        meson = import ../toolchain/meson-filc.nix { inherit pkgs; };
      }
      // extra
    );
}
