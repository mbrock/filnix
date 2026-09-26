# Overlay for Fil-C ported packages
# Converts the port list from ../ports.nix into a nixpkgs overlay

pkgs: final: prev:
let
  portDSL = import ./default.nix { inherit (pkgs) lib pkgs; };
  portList = import ../ports.nix { inherit pkgs prev final; };
in
portDSL.makeOverlay portList final prev
// pkgs.lib.optionalAttrs prev.stdenv.hostPlatform.isFilc {
  # libunwind's unwinder is hand-written assembly without SaRCAsm
  # annotations, and cannot follow Fil-C frames anyway. Packages that check
  # availability (GStreamer, strace, ...) then build without it.
  libunwind = prev.libunwind.overrideAttrs (old: {
    meta = old.meta // {
      badPlatforms = (old.meta.badPlatforms or [ ]) ++ [
        prev.stdenv.hostPlatform.system
      ];
    };
  });

  # Boost 1.87 is the ported release (Context uses ucontext); Nixpkgs'
  # default 1.89 builds its assembly fcontext and fails.
  boost = final.boost187;

  # overrideScope, so that the plugins build against this GStreamer.
  gst_all_1 = prev.gst_all_1.overrideScope (
    gfinal: gprev: {
      # Only the optional PTP clock helper uses Rust. The multimedia core is C.
      gstreamer =
        (gprev.gstreamer.override {
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
    }
  );

  # Nix itself. Boehm GC scans the native stack and data segments, which
  # Fil-C objects do not live in; Fil-C collects garbage itself. seccomp
  # filters and the static busybox sandbox shell are unavailable too.
  nixComponents = prev.nixVersions.nixComponents_2_34.overrideScope (
    nfinal: nprev: {
      nix-expr = nprev.nix-expr.override { enableGC = false; };
      nix-store =
        (nprev.nix-store.override {
          withSandboxShell = false;
          withAWS = false;
        }).overrideAttrs
          (old: {
            buildInputs = builtins.filter (
              dep: !(pkgs.lib.hasInfix "libseccomp" (dep.name or ""))
            ) old.buildInputs;
            mesonFlags = map (
              flag:
              if flag == "-Dseccomp-sandboxing=enabled" then
                "-Dseccomp-sandboxing=disabled"
              else
                flag
            ) old.mesonFlags;
          });
    }
  );
  nix = final.nixComponents.nix-everything;

  tree-sitter = final.callPackage ./tree-sitter.nix {
    inherit (prev) tree-sitter;
  };

  # The scanner executes C dumpers and loads a Python C extension; GLib's
  # gdbus-codegen emits GType operations. Both must match the target GLib ABI
  # even though they run during builds. Explicit scope overrides still win,
  # and the native package set keeps its ordinary tools. Package-set
  # attributes are spliced, so drop __spliced: mkDerivation would otherwise
  # swap in the build platform's tools for nativeBuildInputs.
  newScope =
    extra:
    prev.newScope (
      {
        gobject-introspection = removeAttrs final.gobject-introspection [
          "__spliced"
        ];
        glib = removeAttrs final.glib [ "__spliced" ];
        # mkenums_simple embeds C templates independently of glib-mkenums.
        meson = import ../toolchain/meson-filc.nix { inherit pkgs; };
      }
      // extra
    );
}
