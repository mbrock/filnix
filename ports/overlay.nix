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

  tree-sitter = final.callPackage ./tree-sitter.nix {
    inherit (prev) tree-sitter;
  };
}
