# Build-platform code generators whose output targets Fil-C.
#
# GLib's gdbus-codegen and glib-genmarshal, Meson's mkenums_simple and the
# introspection scanner's gdump.c emit C for the package being built. Under
# Fil-C that C must treat GType as a pointer. Like a compiler, these tools are
# target-dependent, so they are patched for the package set whose target is
# Fil-C (pkgsBuildHost): splicing then selects them for Fil-C
# nativeBuildInputs. The native package set, whose target is not Fil-C, keeps
# its ordinary tools.
#
# GLib and gobject-introspection are native twins of the Fil-C ports, at the
# same versions: generated code must only use APIs the target GLib has, and
# Meson negotiates scanner options by the build GI's version. Only the
# target-neutral parts of the port patches apply; the rest assume Fil-C.
#
# The twins are tools, not libraries for the build platform. Replacing
# pkgsBuildHost's glib would relink every native library there against GLib
# 2.80.4 (Pango, GTK, Qt, glibmm, SDL's PipeWire...), rebuilding them outside
# the binary cache and breaking those that need a newer GLib. So the twins
# are built from pkgsBuildHost but only the Fil-C set's view of it,
# `pkgsBuildHost` (and so `buildPackages` and splicing), names them; native
# packages inside pkgsBuildHost keep the ordinary GLib.
final: prev:
let
  inherit (prev) lib;

  # The ports DSL for package set `pkgs`, applied to one of its packages.
  dsl = pkgs: import ./default.nix { inherit lib pkgs; };
  build =
    pkgs: pkg: steps:
    let
      spec = (dsl pkgs).for pkg steps;
    in
    (pkg.override spec.overrideArgs).overrideAttrs spec.attrs;

  twins =
    bh:
    let
      inherit (dsl bh)
        arg
        use
        pin
        patch
        skipPatch
        ;

      # Select hunks of a port patch by file, keeping one source for them.
      hunks =
        name: portPatch: files:
        bh.runCommand name { nativeBuildInputs = [ bh.patchutils ]; } ''
          filterdiff ${lib.concatMapStringsSep " " (f: "-i '*/${f}'") files} \
            ${portPatch} > $out
          test -s $out
        '';

      glib = build bh bh.glib [
        (pin "2.80.4" "sha256-JOApxd/JtE5Fc2l63zMHipgnxIk4VVAEs7kJb6TqA08=")
        (patch (
          hunks "glib-filc-generators.patch" ../ports/patch/glib-2.80.4.patch [
            "gio/gdbus-2.0/codegen/codegen.py"
            "gobject/glib-genmarshal.in"
          ]
        ))
        (skipPatch "split-dev-programs.patch")
        (patch ../patches/glib-split-backport.patch)
        (arg {
          libsysprof-capture = null;
          # The Fil-C GI port supplies the target GLib GIRs.
          withIntrospection = false;
        })
        (use {
          doCheck = false;
          mesonFlags = [
            "-Ddevbindir=${placeholder "dev"}/bin"
            "-Dglib_debug=disabled"
            "-Ddocumentation=true"
            (lib.mesonBool "dtrace" false)
            (lib.mesonBool "systemtap" false)
            "-Dnls=enabled"
            (lib.mesonEnable "introspection" false)
            "-Dtests=false"
          ];
        })
      ];

      gobject-introspection-unwrapped =
        build bh bh.gobject-introspection-unwrapped
          [
            (arg {
              inherit glib;
              # Only its library path reaches the scanner; keep it the one the
              # twin has always had.
              cairo = bh.cairo.override { inherit glib; };
            })
            (pin "1.80.1" "sha256-od98Qk4VvaGrY5wA6QUbmt9c6hqeUS+KYDtTzRmbxtg=")
            (patch (
              hunks "gobject-introspection-filc-scanner.patch"
                ../ports/patch/gobject-introspection-1.80.1.patch
                [
                  "girepository/gdump.c"
                  "giscanner/ccompiler.py"
                ]
            ))
            (patch ../patches/gobject-introspection-filc-tools.patch)
            (patch ../patches/gobject-introspection-link-environment.patch)
            (use (old: {
              postPatch = (old.postPatch or "") + ''
                # Fil-C GLib's gtype.h provides uintptr_t; native GLib's does not.
                sed -i '/#include <stdio.h>/a #include <stdint.h>' girepository/gdump.c
                # Fil-C builds have no ldd on PATH; the scanner runs it on dumpers.
                substituteInPlace giscanner/shlibs.py \
                  --replace-fail "['ldd', binary.args[0]]" "['${lib.getBin bh.stdenv.cc.libc}/bin/ldd', binary.args[0]]"
              '';
              # Resolve GIR includes against the Fil-C libraries being linked
              # rather than build-platform GIRs, which XDG_DATA_DIRS lists first.
              # The scanner searches GI_GIR_PATH before XDG_DATA_DIRS.
              postFixup = (old.postFixup or "") + ''
                cat >> "$dev/nix-support/setup-hook" <<'EOF'

                _filcTargetGirPath() {
                  if [ -d "$1/share/gir-1.0" ]; then
                    addToSearchPath GI_GIR_PATH "$1/share/gir-1.0"
                  fi
                }
                addEnvHooks "$targetOffset" _filcTargetGirPath
                EOF
              '';
            }))
          ];
    in
    {
      inherit glib gobject-introspection-unwrapped;
      # The Fil-C-targeted wrapper, which the set itself no longer names.
      gobject-introspection = bh.callPackage (
        bh.path + "/pkgs/development/libraries/gobject-introspection/wrapper.nix"
      ) { inherit gobject-introspection-unwrapped; };
    };
in
if prev.stdenv.targetPlatform.isFilc && !prev.stdenv.hostPlatform.isFilc then
  {
    # Meson is not linked by native libraries, so it is patched for the whole
    # set; meson-python there propagates it to Fil-C Python builds.
    meson = build prev prev.meson [
      ((dsl prev).patch ../patches/meson-gtype.patch)
    ];

    # Qt's qmake hook is spliced from this set's buildPackages. Here Qt still
    # differs from the native one without the GLib twin (qttools and so
    # qttranslations reference another qtbase), and a native Qt module here
    # (reached through wrapQtAppsHook, e.g. qtsvg) saw two qtbases: its
    # setup hook failed with "detected mismatched Qt dependencies". Qt
    # emits no GType code, so use the ordinary native Qt, which also comes
    # from cache.nixos.org.
    qt5 = final.buildPackages.qt5;
    libsForQt5 = final.buildPackages.libsForQt5;
    qt6 = final.buildPackages.qt6;
    qt6Packages = final.buildPackages.qt6Packages;
    # Likewise the gobject-introspection wrapper: with a Fil-C target it
    # wraps the scanner for cross use and propagates the Fil-C GI, so native
    # libraries here that link GI (PyGObject, and through it graphene, GTK 4,
    # GStreamer, PipeWire, SDL) left the cache. Fil-C packages get the
    # twin's wrapper from `twins` below.
    gobject-introspection = final.buildPackages.gobject-introspection;
    # PyGObject adds Python's pkg-config path when host != target, meaning
    # when cross-compiled (NixOS/nixpkgs#378447); here that holds natively.
    pythonPackagesExtensions = prev.pythonPackagesExtensions ++ [
      (_: pyprev: {
        pygobject3 = pyprev.pygobject3.overrideAttrs { preConfigure = ""; };
      })
    ];
  }
else if
  prev.stdenv.hostPlatform.isFilc && !prev.stdenv.buildPlatform.isFilc
then
  {
    pkgsBuildHost = prev.pkgsBuildHost // twins prev.pkgsBuildHost;
  }
else
  { }
